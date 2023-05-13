package parseq

// helper class pattern https://softwaremill.com/scala-3-macros-tips-and-tricks/
var indent = 0

trait WithPrint[Q <: quoted.Quotes](val printing: Boolean)(using val quotes: Q):
  import quotes.reflect.*
  import PrintExtensions.*

  object PrintExtensions:
    extension (tree: Tree)
      def showShort: String =
        tree.showShortR(0, showType = false)

      def showShortWithType: String =
        tree.showShortR(0, showType = true)

      def showShortR(max: Int, desc: String = "", showType: Boolean = false): String =
        val string1 = tree.show(using Printer.TreeShortCode)
          .replaceAll("\\[A >: Nothing <: Any] => ([a-zA-Z_]+)\\[A]", "$1")
          //.replace("(fun.Fun$package.listMonad)", "")
          //.replace("(listMonad)", "")
          //.replace("(futureMonad)", "")
        var brack = 0
        val string2 = string1.flatMap { c =>
          if (c == ']') brack -= 1
          val result = if brack > max then None else Some(c)
          if (c == '[') brack += 1
          result }.mkString
        val rest = tree match
        case _: Term if showType =>
          val string4 = TypeTree.of(using tree.asInstanceOf[Term].tpe.asType).show(using Printer.TreeShortCode)
          val string5 = TypeTree.of(using tree.asInstanceOf[Term].tpe.widenTermRefByName.asType).show(using Printer.TreeShortCode)
          val rest = " " + Console.MAGENTA
                   + ": " + string4
                   + (if string5 != string4 then " : " + string5 else "")
                   + Console.RESET
          rest
        case _ => ""
        val string6 = Console.GREEN + desc
                    + Console.RESET + string2
                    + rest
        string6

    extension (tpe: TypeRepr)
      def showType: String =
        Console.MAGENTA
        + TypeTree.of(using tpe.asType).show(using Printer.TreeShortCode)
        + Console.RESET

  object Print:
    def printShort(term: Tree): Unit =
      printShort(term, 0)
  
    def printShort(term: Tree, max: Int, desc: String = ""): Unit =
      printit(term.showShortR(max, desc))
  
    def printShortWithType(term: Tree, desc: String = ""): Unit =
      printit(term.showShortR(0, desc, showType = true))
  
    def printit(ss: String*): Unit =
      println("- ".repeat(indent) +
        ss.mkString(" ").replace("\n", "\n" + "  ".repeat(indent)))
  
    def printType(tpe: TypeRepr): Unit =
      printit(": " + tpe.showType)
  
    def printMedium(term: Tree): Unit =
      //val string1 = term.show(using Printer.TreeAnsiCode)
      val string1: String = term.show(using Printer.TreeShortCode)
        .replaceAll("\\[A >: Nothing <: Any] => ([a-zA-Z_]+)\\[A]", "$1")
        //.replace("(fun.Fun$package.listMonad)", "")
        //.replace("(listMonad)", "")
        //.replace("(FutureSpec.this.futureMonad)", "")
        //.replace("(futureMonad)", "")
      val string2 = new StringBuffer
      var (i, brack, paren, brace) = (0, 0, 0, 0)
      while (i < string1.length) {
        val c = string1(i)
        if (c == '}') { brace -= 1 }
        if (c == '[') { brack += 1; if (brack == 1) string2 append Console.MAGENTA }
        if (c == ')') { paren -= 1; /* string2 append "\n" + "  ".repeat(paren+brace) */ }
        string2 append c
        if (c == '\n') string2 append "  ".repeat(paren)
        //if (c == '=' && string1(i+1) == '>') { i += 2; string2 append ">\n" + "  ".repeat(paren+brace) }
        if (c == ',' && brack == 0) { i += 1; string2 append "\n" + "  ".repeat(paren+brace) }
        if (c == '(')
          if (string1(i+1) == ')') { i += 1; string2 append ')' }
          else if (i>1 && string1(i-1) == '(') { paren += 1 }
          else { paren += 1; string2 append "\n" + "  ".repeat(paren+brace) }
        if (c == ']') { brack -= 1; if (brack == 0) string2 append Console.RESET }
        if (c == '{') { brace += 1 }
        i += 1
      }
      printit(string2.toString)
  
    def printLong(term: Tree, desc: String = ""): Unit =
      printit(Console.GREEN + desc
            + Console.RESET + term.show(using Printer.TreeStructure))
