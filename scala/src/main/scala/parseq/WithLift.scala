package parseq

import scala.annotation.tailrec
import scala.quoted.{Expr, Type}

trait WithLift[Q <: quoted.Quotes, F[_]: Type](evidence: Expr[Monad[F]]) extends WithPrint[Q]:
  import quotes.reflect.*
  import PrintExtensions.*

  object Lift:
    def getMonadTypeFromEvidence(ev: Term): TypeRepr =
      ev.tpe.baseType(markerTypeSym) match
      case AppliedType(_, List(TypeLambda(_, _, AppliedType(monadTypeRepr, List(_))))) => monadTypeRepr
      case AppliedType(_, List(monadTypeRepr)) => monadTypeRepr

    ///////////////////////////////////////////////////////////////////////////////////////////////
    // ADAPTS TO MONAD TYPE
    //Print.printit("INSTANTIATING WITH FOLLOWING MONAD")
    val evidenceTerm: Term = evidence.asTerm
    val markerTypeSym: Symbol = getTypeSym('{ null: Monad[Option] }.asTerm)
    val monadTypeRepr: TypeRepr = getMonadTypeFromEvidence(evidenceTerm)
    //Print.printType(monadTypeRepr)
    //val AppliedType(_, List(monadTypeRepr)) = TypeRepr.of(using summon[Type[F]]).baseType(markerTypeSym)
    ///////////////////////////////////////////////////////////////////////////////////////////////

    object Index:
      def unapply(term: Term): (Term, List[Boolean]) = term match
      case Select(Index(term, n), "_1") => (term, false :: n)
      case Select(Index(term, n), "_2") => (term, true :: n)
      case term => (term, Nil)

    class TupleSubstitution(fromSymbol: Symbol, toTerm: Term) extends TreeMap:
      override def transformTerm(term: Term)(owner: Symbol): Term = term match
      case Index(head, xs) if head.symbol == fromSymbol =>
        safeIndex(toTerm, xs).changeOwner(owner)
      case _ => super.transformTerm(term)(owner)

    class PureSubstitution(fromSymbol: Symbol, toTerm: Term) extends TreeMap:
      override def transformTerm(term: Term)(owner: Symbol): Term = term match
      case term if term.symbol == fromSymbol => toTerm.changeOwner(owner)
      case _ => super.transformTerm(term)(owner)

    def getTypeHead(tpe: TypeRepr): TypeRepr = tpe match
    case AppliedType(head, args) => head

    @tailrec def getTypeSym(expr: Term): Symbol = expr match
    case Inlined(_, _, body) => getTypeSym(body)
    case Typed(expr, tpt) => getTypeHead(tpt.tpe).typeSymbol

    @tailrec def getSym(expr: Term): Symbol = expr match
    case Inlined(_, _, body) => getSym(body)
    case Lambda(_, body) => getSym(body)
    case Apply(body, _) => getSym(body)
    case TypeApply(body, _) => getSym(body)
    case expr => expr.symbol

    def safeIndex(term: Term, xs: List[Boolean]): Term = safeIndexR(term, xs.reverse)
    def safeIndexR(term: Term, xs: List[Boolean]): Term = (xs, term) match
      case (false :: xs, Apply(TypeApply(f, _), List(x, y)))
      if f.symbol == tuple2Sym => safeIndexR(x, xs)
      case (true :: xs, Apply(TypeApply(f, _), List(x, y)))
      if f.symbol == tuple2Sym => safeIndexR(y, xs)
      case (false :: xs, term)        => Select(safeIndexR(term, xs), fstSym)
      case (true :: xs, term)         => Select(safeIndexR(term, xs), sndSym)
      case (Nil, term)                => term

    // term symbols
    private val pureSym      = getSym('{ parseq.pure[List, Any](null)(using null) }.asTerm)
    private val bindSym      = getSym('{ parseq.bind[List, Any, Any](null)(null)(using null) }.asTerm)
    private val fstSym       = getSym('{ (null, null)._1 }.asTerm)
    private val sndSym       = getSym('{ (null, null)._2 }.asTerm)
    private val identitySym  = getSym('{ scala.Predef.identity[Any](null) }.asTerm)
    private val isLinearSym  = getSym('{ isLinear[Any, Any](null) }.asTerm)
    val tuple2Sym            = getSym('{ Tuple2[Any, Any](null, null) }.asTerm)

    // terms
    private val zapTerm      = Ref(getSym('{ parseq.zap[Option, Any, Any](null, null)(using null) }.asTerm))
    private val zipTerm      = Ref(getSym('{ parseq.zip[Option, Any, Any](null, null)(using null) }.asTerm))
    private val fmapTerm     = Ref(getSym('{ parseq.fmap[Option, Any, Any](null, null)(using null) }.asTerm))
    private val bindTerm     = Ref(bindSym)
    private val pureTerm     = Ref(pureSym)
    private val identityTerm = Ref(identitySym)
    private val isLinearTerm = Ref(isLinearSym)

    object IsLinear:
      def apply(fun: Term): Term =
        val Function1Type(argT, resT) = fun.tpe
        Apply(TypeApply(isLinearTerm,
          List(TypeTree.of(using argT.asType), TypeTree.of(using resT.asType))),
          List(fun))
      def unapply(term: Term): Option[Term] =
        term match
        case Apply(TypeApply(islinear, List(a, b)), List(fun))
        if islinear.symbol == isLinearSym => Some(fun)
        case _ => None

    object LinearLambda:
      def apply(owner: Symbol, argTpe: TypeRepr, retTpe: TypeRepr)(body: (Symbol, Term) => Term): Term =
        IsLinear(mkLambda(owner, argTpe, retTpe)(body))
      def unapply(term: Term): Option[(ValDef, Term)] =
        term match
        case IsLinear(Lambda(List(args), expr)) => Some((args, expr))
        case _ => None

    var freshVariableNames: Int = 0
    def mkLambda(owner: Symbol, argTpe: TypeRepr, retTpe: TypeRepr)(body: (Symbol, Term) => Term): Term =
      val methodType = MethodType(List(f"tmp${freshVariableNames += 1; freshVariableNames}%02X"))(_ => List(argTpe), _ => retTpe)
      def methodBody(owner: Symbol, theArgs: List[Tree]): Term =
        val List(theArg: Term) = theArgs
        body(owner, theArg)
      Lambda(owner, methodType, methodBody)

    // hoisting an symbol from a term
    // - create a lambda around the term,
    // - apply the lambda to the symbol
    // - replace the symbol in the term with the argument of the lambda
    def hoist(vd: ValDef, body: Term)(owner: Symbol): Term =
      mkLambda(owner, Ref(vd.symbol).tpe.widenTermRefByName, body.tpe) { case (owner, theArg) =>
        Block(ValDef.copy(vd)(vd.name, TypeTree.of(using vd.rhs.get.tpe.widen.asType), Some(theArg)) :: Nil,
          body).changeOwner(owner)
        //ValDef.let(Symbol.newVal(owner, "new", vd.tpt.tpe, vd.symbol.flags, Symbol.noSymbol), "new", theArg) { ref =>
        //  new PureSubstitution(vd.symbol, ref).transformTerm(body.changeOwner(owner))(owner) }
      }

    private def safeBeta(f: Term, x: Term)(owner: Symbol): Term = f match
    case Identity() => x
    case IsLinear(f) => // function was linear, therefore we can enforce inlining at no cost
      val call = Apply(Select.unique(f, "apply"), List(x))
      val tmp = Term.betaReduce(call)
      val res = tmp match
      case Some(Block((vd @ ValDef(name, tpt, Some(rhs))) :: stats, body)) =>
        TupleSubstitution(vd.symbol, rhs).transformTerm(Block(stats, body))(owner)
      case Some(tree) => tree        // why does this happen?
      case None       => ??? // call // should not happen
      if (printing)
        tmp.foreach { tmp => Print.printShortWithType(tmp, desc="before ") }
        Print.printShortWithType(res, desc="after  ")
      res
    case _ =>
      val call = Apply(Select.unique(f, "apply"), List(x))
      Term.betaReduce(call) match
      case Some(x) => x
      case None => call


    def join(ffa: Term)(owner: Symbol): Term =
      val MonadType(yarg) = ffa.tpe
      bind(Identity(owner, yarg), ffa)(owner)

    // [x -> y] -> [x] -> [y]
    def zap(f: Term, x: Term)(owner: Symbol): Term =
      Print.printType(f.tpe)
      Print.printType(x.tpe)
      val MonadType(Function1Type(xarg, yarg)) = f.tpe // x -> y
      val MonadType(xarg2) = x.tpe // x
      assert(xarg <:< xarg2)
      Apply(Apply(TypeApply(zapTerm, List(
        TypeTree.of(using monadTypeRepr.asType),
        TypeTree.of(using xarg.asType),
        TypeTree.of(using yarg.asType))),
      List(f, x)), List(evidenceTerm))

    // [x] -> [y] -> [x × y]
    def zip(x: Term, y: Term)(owner: Symbol): Term =
      def tup2(x: TypeRepr, y: TypeRepr): TypeRepr =
        TypeIdent(defn.TupleClass(2)).tpe.appliedTo(List(x, y))
      val MonadType(xarg) = x.tpe
      val MonadType(yarg) = y.tpe
      val ret1 = MonadType(tup2(xarg, yarg))
      val ret2 = MonadType(tup2(xarg, yarg))
      bind(LinearLambda(owner, xarg, ret1) { case (owner, x2) =>
        bind(LinearLambda(owner, yarg, ret2) { case (owner, y2) =>
          Lift.Pure(Apply(TypeApply(Ref(tuple2Sym), List(
            TypeTree.of(using xarg.widen.asType),
            TypeTree.of(using yarg.widen.asType))),
            List(x2, y2)), evidenceTerm)
        }, y.changeOwner(owner))(owner)
      }, x)(owner)

    def zipReal(x: Term, y: Term): Term =
      val MonadType(xarg) = x.tpe
      val MonadType(yarg) = y.tpe
      Apply(Apply(TypeApply(zipTerm, List(
        TypeTree.of(using monadTypeRepr.asType),
        TypeTree.of(using xarg.asType),
        TypeTree.of(using yarg.asType))),
      List(x, y)), List(evidenceTerm))

    def fmapReal(fa: Term, ab: Term): Term =
      val MonadType(faarg) = fa.tpe
      val MonadType(abarg) = ab.tpe
      Apply(Apply(TypeApply(fmapTerm, List(
        TypeTree.of(using monadTypeRepr.asType),
        TypeTree.of(using faarg.asType),
        TypeTree.of(using abarg.asType))),
      List(fa, ab)), List(evidenceTerm))

    // (x -> [y]) -> ([x] -> [y])
    //def m_bind[A: Type, B: Type](x: Expr[List[A]], f: Expr[A => List[B]]): Expr[List[B]] =
    def bind(f: Term, x: Term)(owner: Symbol): Term =
      // right:         a >>= pure     =     a
      // left:        pure a >>= f     =     f a
      // assoc:    (a >>= b) >>= c     =     a >>= (\x. b x >>= c)
      (x, f) match
      case (Pure(x, ev), f) => // TODO check right ev
        safeBeta(f, x)(owner)
      case (Bind(x, f, ev), g) =>
        val Function1Type(argType, _) = f.tpe
        val Function1Type(_, retType) = g.tpe
        val lambda = mkLambda(owner, argType, retType){ case (owner, theArg) =>
          val gg = g.changeOwner(owner)
          val ff = f.changeOwner(owner)
          this.bind(gg, safeBeta(ff, theArg)(owner))(owner) } // TODO not in tail position? :(
        this.bind(lambda, x)(owner)
      case (x, Lambda(List(x1), Pure(x2, ev))) if x2.symbol == x1.symbol => // TODO check right ev
        x
      case (x, f) =>
        this.Bind(f, x, evidenceTerm)

    @tailrec def nth(expr: Term, i: Int, len: Int): Term =
      if i==1 && len==1 then expr
      else if i==1 then Select(expr, fstSym)
      else if i<0 || len<0 then ???
      else nth(Select(expr, sndSym), i-1, len-1)

    def hasSym(f: Statement, symbol: Symbol): Boolean = f match
    case TypeApply(Select(o, "apply"), _) => o.symbol == symbol
    case TypeApply(o, _) => o.symbol == symbol
    case o => o.symbol == symbol

    ///////////////////////////////////////////////////////////////////////////////////////
    class MonadTypeGen(monadTypeRepr: TypeRepr):
      def apply(x: TypeRepr): TypeRepr =
        monadTypeRepr.appliedTo(List(x))
      def unapply(tree: TypeRepr): scala.Tuple1[TypeRepr] = tree.widenTermRefByName match
      case AppliedType(head, List(arg)) =>
        //assert(head <:< monadTypeRepr,
        //  "" + head.showShortType + " <:< " + monadTypeRepr.showShortType)
        Tuple1(arg)
    object MonadType extends MonadTypeGen(monadTypeRepr)

    object Pure:
      def apply(x: Term, ev: Term): Term =
        val myMonadTypeRepr = getMonadTypeFromEvidence(ev)
        val result = Apply(Apply(TypeApply(pureTerm, List(
          TypeTree.of(using myMonadTypeRepr.asType),
          TypeTree.of(using x.tpe.widen.asType))),
        List(x)), List(ev))
        result
      def unapply(expr: Term): Option[(Term, Term)] = expr match
        case Inlined(_, _, Pure(x, ev)) => Some((x, ev))
        case Typed(Pure(x, ev), _)      => Some((x, ev))
        case Apply(Apply(TypeApply(ff, _), List(x)), List(ev))
        if hasSym(ff, pureSym) => Some((x, ev))
        case _ => None

    object Bind:
      def apply(f: Term, x: Term, ev: Term): Term =
        val myMonadTypeRepr = getMonadTypeFromEvidence(ev)
        val MyMonadType = MonadTypeGen(myMonadTypeRepr)
        val Function1Type(argTpe, MyMonadType(yarg)) = f.tpe
        val MyMonadType(xarg) = x.tpe.widenTermRefByName
        Apply(Apply(Apply(TypeApply(bindTerm, List(
          TypeTree.of(using myMonadTypeRepr.asType),
          TypeTree.of(using xarg.widen.asType),
          TypeTree.of(using yarg.widen.asType))),
        List(x)), List(f)), List(ev))
      def unapply(expr: Term): Option[(Term, Term, Term)] = expr match
        case Apply(Apply(Apply(TypeApply(ff, _), List(f)), List(x)), List(ev))
        if hasSym(ff, bindSym) => Some((f, x, ev))
        case _ => None
    ///////////////////////////////////////////////////////////////////////////////////////

    object Function1Type:
      def unapply(tree: Term): (TypeRepr, TypeRepr) = tree match
      case AppliedType(head @unchecked, List(arg, ret)) =>
        assert(head.show == "scala.Function1", head.show) // TODO better than string match?
        (arg, ret)

    object Applies:
      // arguments are either 1. arguments or 2. varargs (e.g., lists of arguments)...
      def copy(expr: Term)(head: Term, meth: Option[Symbol], params: List[TypeTree], argss: List[List[Either[Term, List[Term]]]]): Term =
        (expr, meth, params, argss) match
        case (Apply(head2, _), meth, params, args :: argss) =>
          Apply.copy(expr)(Applies.copy(head2)(head, meth, params, argss), args.map {
            case Right(repeatlist) => Repeated(repeatlist, TypeTree.of(using repeatlist.head.tpe.asType))
            case Left(argument) => argument
          })
        case (TypeApply(_, _), None, params, Nil) if params.nonEmpty =>
          TypeApply.copy(expr)(head, params)
        case (Select(_, _), Some(meth), Nil, Nil) =>
          Select.copy(expr)(head, meth.name)
        case (_, None, Nil, Nil) =>
          head
      def unapply(expr: Term): (Term, Option[Symbol], List[TypeTree], List[List[Either[Term, List[Term]]]]) =
        expr match
        case Apply(Applies(f, m, ts, xss), xs) => (f, m, ts, xs.map {
          case Typed(Repeated(repeatlist, tpt2), tpt1) => Right(repeatlist)
          case argument => Left(argument)
        } :: xss)
        case TypeApply(f, ts) => (f, None, ts, Nil)
        case om@Select(o, m) => (o, Some(om.symbol), Nil, Nil)
        case _ => (expr, None, Nil, Nil)

    object NiceApplies:
      def copy(expr: Term)(head: Term, meth: Option[Symbol], params: List[TypeTree], argss: List[Term], structure: List[List[Either[Unit, List[Unit]]]]): Term =
        Applies.copy(expr)(head, meth, params, conjoin(argss, structure))
      def unapply(expr: Term): (Term, Option[Symbol], List[TypeTree], List[Term], List[List[Either[Unit, List[Unit]]]]) =
        val Applies(f, m, ts, xss) = expr
        val (values, structure) = separate(xss)
        (f, m, ts, values, structure)
      def separate(xxs: List[List[Either[Term, List[Term]]]]): (List[Term], List[List[Either[Unit, List[Unit]]]]) =
        val content: List[Term] = xxs.flatMap { xs => xs.flatMap {
          case Left(value) => List(value)
          case Right(value) => value
        } }
        val structure: List[List[Either[Unit, List[Unit]]]] = xxs.map { xs => xs.map {
          case Left(value) => Left(())
          case Right(value) => Right(value.map { x => () })
        } }
        (content, structure)
      def conjoin(ocontent: List[Term], structure: List[List[Either[Unit, List[Unit]]]]): List[List[Either[Term, List[Term]]]] =
        var content = ocontent
        def pop(): Term =
          val head :: tail = content
          content = tail
          head
        structure.map { xs => xs.map {
          case Left(_) => Left(pop())
          case Right(value) => Right(value.map { xs => pop() })
        } }


    object Call:
      def unapply(expr: Term): Option[(Term, TypeRepr, List[Term])] = expr match
      case Apply(ff @ TypeApply(Select(f, "apply"), _), xs) => Some((ff, f.tpe, xs))
      case _ => None

    object Identity:
      def apply(owner: Symbol, tpe: TypeRepr) =
        mkLambda(owner, tpe, tpe){ case (owner, theArg) => theArg }
      def unapply(term: Term): Boolean = term match
      case Lambda(List(arg), body) if body.symbol == arg.symbol => true
      case _ => false

    object PotBlock:
      def apply(b: List[Statement], e: Term): Term = b match
      case Nil => e
      case xs => Block(xs, e)
      def unapply(t: Term): (List[Statement], Term) = t match
      case Block(bs, e) => (bs, t)
      case e => (Nil, e)

    object Stable:
      def unapply(t: Tree): Option[Tree] = t match
      case Select(Stable(_), _) => Some(t)
      case _: Literal => Some(t)
      case _: TypeApply => Some(t)
      case _: Ident => Some(t)
      //case _: Function => Some(t)
      case _ => None