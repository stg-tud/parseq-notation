package parseq

///////////////////////////////////////////////////////////////////////////////
// low-level type classes

trait Monad[F[_]]:
  def pureImpl[A](a: A): F[A]
  def bindImpl[A, B](fa: F[A])(f: A => F[B]): F[B]
//def joinImpl[A](ffa: F[F[A]]): F[A]

trait TryCatchMonad[F[_]] extends Monad[F]:
  def tryCatch[A,B](t: F[A])(c: PartialFunction[Throwable, B]): F[B]
trait TryFinallyMonad[F[_]] extends Monad[F]:
  def tryFinally[A,B](t: F[A])(c: PartialFunction[Throwable, B]): F[B]

trait Extractor[F[_]: Monad]:
  def apply[A](a: F[A]): A

def isLinear[A,B](f: A => B): A => B =
  f

///////////////////////////////////////////////////////////////////////////////
// high-level interface

def pure[F[_]: Monad, A](a: A): F[A] = summon[Monad[F]].pureImpl(a)
def bind[F[_]: Monad, A, B](fa: F[A])(f: A => F[B]): F[B] = summon[Monad[F]].bindImpl(fa)(f)
def fmap[F[_]: Monad, A, B](fa: F[A], f: A => B): F[B] = bind(fa)(f andThen pure)
def zap[F[_]: Monad, A, B](ff: F[A => B], fa: F[A]): F[B] = bind(ff)(f => bind(fa)(a => pure(f(a))))
//object join { def apply[F[_]: Monad, A](ffa: F[F[A]]): F[A] = summon[Monad[F]].joinImpl(ffa) }
//inline def fmap[F[_]: Monad, A, B](inline fa: F[A])(inline f: A => B): F[B] = bind(fa)(f andThen pure)
inline def flap[F[_]: Monad, A, B](inline f: F[A => B])(inline a: A): F[B] = bind(f)(f => pure(f(a)))
inline def zip[F[_]: Monad, A, B](inline ff: F[A], inline fa: F[B]): F[(A,B)] = bind(ff)(f => bind(fa)(a => pure((f, a))))
inline def join[F[_]: Monad, A](inline ffa: F[F[A]]): F[A] = bind(ffa)(identity)

//extension[F[_]: Monad, A] (fa: F[A])
  //def bind[B](f: A => F[B]): F[B] = summon[Monad[F]].bind(fa)(f)
  //def fmap[B](f: A => B): F[B] = summon[Monad[F]].fmap(fa)(f)
//  @compileTimeOnly("extr needs to be wrapped in a do")
//extension[F[_]: Monad, A, B] (fab: F[A => B])
//  def ap(fa: F[A]): F[B] = fab bind fa.fmap

///////////////////////////////////////////////////////////////////////////////
// instances

given listMonad: Monad[List] with
  override def pureImpl[A](a: A): List[A] =
    List(a)
  override def bindImpl[A, B](fa: List[A])(f: A => List[B]): List[B] =
    fa.flatMap(f)

case class MySet[X](s: Set[X])

given setMonad: Monad[MySet] with
  override def pureImpl[A](a: A): MySet[A] =
    MySet(Set(a))
  override def bindImpl[A, B](fa: MySet[A])(f: A => MySet[B]): MySet[B] =
    MySet(fa.s.flatMap(x => f(x).s))

type State[S] = [A] =>> S => (A, S)
given stateMonad[S]: Monad[State[S]] with
  override def pureImpl[A](a: A): State[S][A] =
    (s:S) => (a, s)
  override def bindImpl[A, B](fa: State[S][A])(f: A => State[S][B]): State[S][B] =
    (s:S) => { val (a,s2) = fa(s); f(a)(s2) }
