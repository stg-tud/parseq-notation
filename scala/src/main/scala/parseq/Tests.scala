package parseq

import scala.annotation.{compileTimeOnly, showAsInfix}
import scala.collection.mutable.ListBuffer
import scala.compiletime.{constValue, erasedValue}

@main def main(): Unit =

  def list1[A](x0:A): List[A] = List(x0)
  def list2[A](x0:A, x1:A): List[A] = List(x0,x1)
  def list3[A](x0:A, x1:A, x2:A): List[A] = List(x0,x1,x2)

  def set1[A](x0:A): MySet[A] = MySet(Set(x0))
  def set2[A](x0:A, x1:A): MySet[A] = MySet(Set(x0,x1))
  def set3[A](x0:A, x1:A, x2:A): MySet[A] = MySet(Set(x0,x1,x2))

  final case class Test[X](title: String, actual: X, expected: X)
  val tests = new ListBuffer[Test[_]]

  {
    val a = list2(1,2)
    val b = list2(1,2)
    tests append Test("purify each/pure eliminates?",
      actual =
        purify { (each: Extractor[List]) =>
          (each(pure((each(a) + each(b)))) +
           each(pure((each(a) + each(b)))))
        },
      expected =
        purify { (each: Extractor[List]) =>
          ((((each(a) + each(b)))) +
           (((each(a) + each(b)))))
        },
      )

    tests append Test("purify each/pure eliminates?",
      actual =
        purify { (each: Extractor[List]) =>
          each(pure(1))
        },
      expected = List(1),
      )
  }


  tests append Test("purify 1+1",
    actual =
      purify { (each: Extractor[List]) =>
        each(list1(1)) + each(list1(1)) },
    expected =
      List(2)
  )

  tests append Test("purify 1 2 + 3 4",
    actual =
      purify { (each: Extractor[List]) =>
        each(list2(1, 2)) + each(list2(3, 4)) },
    expected =
      List(4,5,5,6)
  )

  tests append Test("purify bind",
    actual =
      purify { (each: Extractor[List]) =>
        bind(list2(0, 1))(theArg => pure(Some(theArg))(using listMonad)) },
    expected =
      List(List(Some(0), Some(1)))
  )

  tests append Test("purify blocks",
    actual =
      purify( { (each: Extractor[List]) =>
        val q = each(list1(3))
        val p = 0
        val r = each(list1(6))
        Some(each(list3(p, q, r)) + each(list3(0, 1, 2))) }, debug=false),
    expected =
      List(Some(0), Some(1), Some(2), Some(3), Some(4), Some(5), Some(6), Some(7), Some(8))
  )

  tests append Test("nested II",
    actual =
      purify { (eachSet: Extractor[MySet]) =>
        purify { (eachList: Extractor[List]) =>
          eachList(eachSet(set3(list2(1,2), list1(4), list3(0,5,2)))) }},
    expected =
      MySet(Set(List(1, 2), List(4), List(0, 5, 2)))
  )

  tests append Test("purify extr extr extr",
    actual =
      purify { (extr: Extractor[List]) =>
        extr(extr(list3(extr(list2(list2(0,1), list2(2,3))),
                        extr(list2(list2(4,5), list2(6,7))),
                        extr(list2(list2(8,9), list2(10,11)))))) },
    expected =
      List(0, 1, 4, 5, 8, 9, 0, 1, 4, 5, 10, 11, 0, 1, 6, 7, 8, 9, 0, 1, 6, 7, 10, 11,
           2, 3, 4, 5, 8, 9, 2, 3, 4, 5, 10, 11, 2, 3, 6, 7, 8, 9, 2, 3, 6, 7, 10, 11)
  )

  tests append Test("purify if/else body .5",
    actual =
      purify { (extr: Extractor[List]) =>
        val p = extr(list1(0))
        val q = if true
        then 2
        else 2
        Some(extr(list2(p, q)) + extr(list2(0, 1))) },
    expected =
      List(Some(0), Some(1), Some(2), Some(3))
  )

  tests append Test("purify if/else body",
    actual =
      purify { (extr: Extractor[List]) =>
        val p = extr(list1(0))
        val q = if 10 > 0
        then extr(list1(2))
        else extr(list1(2))
        Some(extr(list2(p, q)) + extr(list2(0, 1))) },
    expected =
      List(Some(0), Some(1), Some(2), Some(3))
  )

  tests append Test("purify if/else condition",
    actual =
      purify { (extr: Extractor[List]) =>
        val p = extr(list1(0))
        val q = if extr(list2(true, false))
        then extr(list1(2))
        else extr(list1(4))
        extr(list2(p, q)) + extr(list2(0, 1)) },
    expected =
      List(0,1,2,3, 0,1,4,5)
  )

  tests append Test("purify extr valdef correctly updates scope",
    actual =
      purify( { (extr: Extractor[List]) =>
        val p = extr(list1(1))
        val bbq = 5
        bbq }),
    expected =
      List(5)
  )

  tests append Test("purify extr stmt correctly updates scope",
    actual =
      purify( { (extr: Extractor[List]) =>
        extr(list1(1))
        val bbq = 5
        bbq }),
    expected =
      List(5)
  )

  tests append Test("purify valdef of blocks",
    actual =
      purify( { (extr: Extractor[List]) =>
        extr(list1(2))
        val bbb = {1; 2; 3; 4; 5}
        2; 3; 4;
        identity(bbb) }),
    expected =
      List(5)
  )

  tests append Test("purify valdef of blocks of unit type, compilercrash",
    actual =
      purify { (extr: Extractor[List]) =>
        val b: Unit = {1; 2}
        identity(b) },
    expected =
      List(())
  )

  tests append Test("purify vardef simple",
    actual =
      purify({ (extr: Extractor[List]) =>
        var b = 1
        b = 2
        b }, debug=false),
    expected =
      List(2)
  )

  tests append Test("purify vardef extr",
    actual =
      purify ({ (extr: Extractor[List]) =>
        var bb = extr(list1(1))
        bb = 2
        bb = 3
        bb = 4
        extr(list1(bb)) }, debug=false),
    expected =
      List(4)
  )

  /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// /// ///
  println()
  println("Test results:")
  tests.foreach { test =>
    val check = test.actual == test.expected
    if check then
      println(s" - ${Console.GREEN}SUCCESS${Console.RESET} " + test.title)
    else
      println(s" - ${Console.RED}FAIL${Console.RESET}    " + test.title)
      println("    actual   = " + test.actual)
      println("    expected = " + test.expected)
  }
  println()
