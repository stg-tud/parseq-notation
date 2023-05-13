package parseq

import scala.annotation.{compileTimeOnly, showAsInfix, tailrec}
import scala.collection.mutable.ListBuffer
import scala.compiletime.ops.int.*
import scala.compiletime.{constValue, erasedValue}
import scala.quoted.*

inline def purify[F[_]: Monad, A](inline expr: Extractor[F] => A, inline debug: Boolean = false): F[A] =
  ${ theMacro('expr, '{ summon[Monad[F]] }, 'debug) }

private def theMacro[F[_]: Type, A: Type](expr: Expr[Extractor[F] => A], evidence: Expr[Monad[F]], debug: Expr[Boolean])(using quotes: Quotes): Expr[F[A]] = {
  import quotes.reflect.*
  val Helper = new WithPrint[quotes.type](debug.value.get) with WithLift[quotes.type, F](evidence)
  import Helper.{Print, Lift}
  import Helper.Lift.{Pure, Applies, NiceApplies, MonadType, Stable, PureSubstitution}
  import Helper.PrintExtensions.*

  if (Helper.printing) Print.printit()
  val Inlined(_, _, Block(List(), Lambda(List(extrDef: ValDef), body))) = expr.asTerm
  val extrSym: Symbol = extrDef.symbol // extr : M a -> a
  val extrTerm: Term = Ref(extrSym)

  object Extr:
    def apply(x: Term): Term =
      val result = Apply(Apply(TypeApply(extrTerm, List(
        TypeTree.of(using Lift.monadTypeRepr.asType),
        TypeTree.of(using x.tpe.widen.asType))),
      List(x)), List(Lift.evidenceTerm))
      result
    def unapply(expr: Term): Option[Term] = expr match
      case Apply(f, List(x))
      if Lift.hasSym(f, extrSym) =>
        Some(x)
      case _ => None

  def isPure(x: Term): Boolean = x match
  case Pure((_, ev)) => true // should check x
  case _ => false

  object PureTransform extends TreeMap:
    def funApp(whole: Term, obj: Term, meth: Option[Symbol], params: List[TypeTree], args: List[Term],
               argStructure: List[List[Either[Unit, List[Unit]]]])(owner: Symbol): Term = {
      val args2 = transformTerm(obj)(owner) :: args.map(transformTerm(_)(owner))
      if false then
        ((obj :: args) zip args2) foreach { case (l, r) =>
          Print.printit(s"${Console.GREEN}arg: pure(${Console.RESET}${l.showShort}${Console.GREEN})${Console.RESET} = ${r.showShort}") }
      val args3 = args2.filterNot(isPure) // TODO need to check ev?
      args3.reduceRightOption { case (hd, tl) => Lift.zip(hd, tl)(owner) } match
      case None => // shortcut
        Lift.Pure(whole, Lift.evidenceTerm)
      case Some(args4) =>
        val MonadType(argType) = args4.tpe
        val retType = whole.tpe
        val lambda = Lift.LinearLambda(owner, argType, retType) { case (owner, theArg) =>
          var i = 0
          def pop(arg1: Term): Term = arg1 match
            case Pure((x, ev)) => x // TODO need to check ev? should not be needed, because we just generated it ourselves?
            case _ => { i += 1; Lift.nth(theArg, i, args3.length) }
          val obj5 = pop(args2.head)
          val args5 = args2.tail map pop
          NiceApplies.copy(whole)(obj5, meth, params, args5, argStructure)
        }
        val result = Lift.zap(Lift.Pure(lambda, Lift.evidenceTerm), args4)(owner)
        println("applies <- " + result.showShortR(1))
        result
    }

    override def transformTerm(tree: Term)(owner: Symbol): Term = try {
      indent += 1
      if (Helper.printing) Print.printShortWithType(tree)

      val result: Term = tree match
      case Stable(_) => // short cut
        Lift.Pure(tree, Lift.evidenceTerm)

      case Extr(x) =>
        Lift.join(transformTerm(x)(owner))(owner) // pure(extr(x)) -> join(pure(x))

      // Applies(o,m,p,a) := Apply*(TypeApply?(Select?(o, m), p), a)
      case NiceApplies(obj, meth, params, args, structure) if meth.nonEmpty || structure.nonEmpty =>
        funApp(tree, obj, meth, params, args, structure)(owner)

      // shift type by the monad type
      case Typed(expr, tpt) =>
        Typed.copy(tree)(transformTerm(expr)(owner),
          TypeTree.of(using Lift.MonadType(TypeRepr.of(using tpt.tpe.asType)).asType))
      case Repeated(elems, tpt) =>
        Repeated.copy(tree)(transformTerms(elems)(owner),
          TypeTree.of(using Lift.MonadType(TypeRepr.of(using tpt.tpe.asType)).asType))

      // atoms
      case Ident(name)       => Lift.Pure(tree, Lift.evidenceTerm)
      case This(qual)        => Lift.Pure(tree, Lift.evidenceTerm)
      case Literal(const)    => Lift.Pure(tree, Lift.evidenceTerm)
      case New(tpt)          => Lift.Pure(tree, Lift.evidenceTerm) // New.copy(tree)(transformTypeTree(tpt)(owner)))
      case Super(qual, mix)  => Lift.Pure(tree, Lift.evidenceTerm) // Super.copy(tree)(transformTerm(qual)(owner), mix)
      case Lambda(tpt, body) => Lift.Pure(tree, Lift.evidenceTerm) // NOTE should come before Block+DefDef !
      case Assign(lhs, rhs)  =>
        Pure(Assign.copy(tree)(lhs, rhs), Lift.evidenceTerm)

      // higher-order
      case Block(Nil, expr) =>
        transformTerm(expr)(owner)
      case Block((vd @ ValDef(name, tpt, Some(rhs))) :: stats, expr) =>
        val hd2 = transformTerm(rhs)(owner)
        val tl2 = Lift.hoist(vd, transformTerm(Block(stats, expr))(owner))(owner)
        Lift.bind(tl2, hd2)(owner)
      case Block((dd @ DefDef(name, args, tpt, rhs)) :: stats, expr) =>
        Block(dd :: Nil, transformTerm(Block(stats, expr))(owner))
      case Block((hd: Term) :: stats, expr) =>
        val hd2 = transformTerm(hd)(owner)
        val tl2 = Lift.mkLambda(owner, hd.tpe.widen, MonadType(tree.tpe.widen)) {
          case (owner, theArg) => transformTerm(Block(stats, expr))(owner).changeOwner(owner) }
        Lift.bind(tl2, hd2)(owner)
      case If(cond, thenp, elsep) =>
        val argument = transformTerm(cond)(owner)
        val lambda = Lift.mkLambda(owner, cond.tpe, MonadType(tree.tpe)){ case (owner, theArg) =>
          If.copy(tree)(theArg, transformTerm(thenp)(owner), transformTerm(elsep)(owner)).changeOwner(owner) }
        Lift.bind(lambda, argument)(owner)

      case Match(selector, cases) => ???
      case Return(expr, from) => ???
      case While(cond, body) => ???
      case Try(block, cases, finalizer) => ???

      // transparent
      case tree: NamedArg =>
        NamedArg.copy(tree)(tree.name, transformTerm(tree.value)(owner))
      case Inlined(call, bindings, expansion) =>
        Inlined.copy(tree)(call, transformSubTrees(bindings)(owner), transformTerm(expansion)(owner))

      if (Helper.printing) Print.printShort(result)
      indent -= 1
      result

    } catch { case e: ClassCastException =>
      Print.printit("!!! ClassCastException")
      e.printStackTrace()
      Print.printShort(tree)
      quotes.reflect.report.errorAndAbort("ClassCastException", tree.pos)
    }

  val result3: Tree = PureTransform.transformTree(body)(Symbol.spliceOwner)
  indent = 0
  if (Helper.printing) {
    Print.printMedium(body)
    Print.printMedium(result3)
    Print.printit("THE END")
    Print.printit()
  }

  result3.asExprOf[F[A]]
}
