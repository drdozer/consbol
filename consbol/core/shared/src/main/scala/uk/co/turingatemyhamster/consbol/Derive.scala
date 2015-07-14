package uk.co.turingatemyhamster.consbol

import uk.co.turingatemyhamster.consbol.util.FuncName

import scala.language.higherKinds
import scalaz._
import scalaz.Scalaz._

import Derive._
import Tell.TellOps

case class DerivationState[M](cuts: Set[Any] = Set.empty,
                              refuted: Map[Set[Any], Set[Any]] = Map.empty,
                              m0: M)
{
  def withModel(m1: M): DerivationState[M] = copy(m0 = m1)
  def withCuts(cs: Set[Any]): DerivationState[M] = copy(cuts = cs)
  def withCut(c: Any): DerivationState[M] = copy(cuts = cuts + c)
}

trait DeriveLHS[A[_], T, M] {
  def apply(lhs: T): DerivationStep[A[T], M]
}

object DeriveLHS {

  implicit def lhsFromRanges[A[_], R, M]
  (implicit
   ops: BinOp[A, R],
   d: Derive[A[R], M],
    r: Ranges[R, M],
    t: Tell[A[R], M],
    fn: FuncName)
  : DeriveLHS[A, R, M] = new DeriveLHS[A, R, M] {

    override def apply(lhs: R): DerivationStep[A[R], M] = {
      allRanges[A[R], R, M] { rhs =>
        ops.recompose(lhs, rhs) derive (d => d, p => p)
      }
    }
  }

}


trait Derive[A, M] {
  def apply(a: A, ds: DerivationState[M]): DerivationResults[A, M]
}

object Derive extends DeriveImplicits with DeriveLowPriorityImpicits {

  type DProof[A] = Disproof[A] \/ Proof[A]
  type DerivationStep[A, M] = DerivationState[M] => DerivationResults[A, M]
  type DerivationResults[A, M] = TrueStream[(DProof[A], DerivationState[M])]

  def apply[A, M](d: A => DerivationStep[A, M])
                 (implicit fn: FuncName): Derive[A, M] = new Derive[A, M]
  {
    override def apply(a: A, ds0: DerivationState[M]): DerivationResults[A, M] =
      d(a)(ds0)
  }

  implicit class TrueStreamOps[A, M](val _s: Derive[A, M]) {
    def ||(_t: Derive[A, M]) = new Derive[A, M] {
      override def apply(a: A, ds0: DerivationState[M]): DerivationResults[A, M] = {
        val k1 = _s(a, ds0)
        k1 mappend {
          val m1 = lastModel(k1, ds0.m0)
          _t(a, ds0 withModel m1)
        }
      }
    }

    def log(implicit fn: FuncName): Derive[A, M] = Derive[A, M] { a => ds0 =>
        println(s"${" " * ds0.cuts.size}${fn.name} [$a] ${ds0.cuts contains a} ${ds0.cuts} ${ds0.refuted}")
        _s(a, ds0)
    }
  }

  implicit class TrueStreamOps0[O[_], T, M](val _s: Derive[O[T], M]) {
    def swap(implicit b: BinOp[O, T], fn: FuncName): Derive[O[T], M] = Derive[O[T], M] { a => ds0 =>
        val (l, r) = b.decompose(a)
        val i = b.recompose(r, l)
        _s(i, ds0)
    }

    def sym(implicit b: BinOp[O, T], fn: FuncName): Derive[O[T], M] =
      _s || _s.swap
  }

  def guard[A, M](d: Derive[A, M])(implicit fn: FuncName) = Derive[A, M] { a => ds0 =>
      if(ds0.cuts contains a)
      {
        println(s"guard $a ${ds0.cuts} !")
        (DProof.cut(a, ds0.cuts) -> ds0).point[TrueStream]
      }
      else
      {
        println(s"guard $a ${ds0.cuts}")
        d(a, ds0 withCut a) map (ds => (DProof1(a, ds._1), ds._2 withCuts ds0.cuts))
      }
  }

  def known[A[_], T, M]
  (implicit k: Know[A, T, M], fn: FuncName) = Derive[A[T], M] { a => ds0 =>
      k(a, ds0.m0) map
         (_ -> ds0)
  }

  def onlyIf[A, B, M](p: Boolean)(f: DerivationStep[B, M])
  : DerivationStep[B, M] =
    if(p)
      f
    else
      _ => StreamT.empty

  def derivationStep[A, B, M](rs: DerivationResults[A, M],
                              fd: Disproof[A] => DerivationStep[B, M],
                              fp: Proof[A] => DerivationStep[B, M])
                             (implicit fn: FuncName)
  : DerivationResults[B, M] = rs flatMap {
    case (s1O, ds1) =>
      s1O fold(
        d => d.left,
        p => if(ds1.cuts contains p.goal) DProof.cut(p.goal, ds1.cuts) else p.right
      ) fold(
        d => fd(d)(ds1),
        p => fp(p)(ds1))
  }

  implicit class AssertionOps[A](val _a: A) {
    def derive[B, M](fd: Disproof[A] => DerivationStep[B, M],
                    fp: Proof[A] => DerivationStep[B, M])
                    (implicit d: Derive[A, M], fn: FuncName): DerivationStep[B, M] = ds0 =>
      derivationStep(d(_a, ds0), fd, fp)
  }

  implicit class ValueOps[L](val _lhs: L) {
    def deriveLHS[A[_]] = new {
      def apply[B, M](fd: Disproof[A[L]] => DerivationStep[B, M])
                     (fp: Proof[A[L]] => DerivationStep[B, M])
                     (implicit d: DeriveLHS[A, L, M], fn: FuncName): DerivationStep[B, M] = ds0 =>
        derivationStep(d(_lhs)(ds0), fd, fp)
    }

    def knowLHS[A[_]] = new {
      def apply[B, M](fd: Disproof[A[L]] => DerivationStep[B, M],
                      fp: Proof[A[L]] => DerivationStep[B, M])
                     (implicit k: Know[A, L, M], fn: FuncName): DerivationStep[B, M] = { ds0 =>
        k.byLHS(_lhs, ds0.m0) map
          (_.fold(
            d => d.left,
            p => if(ds0.cuts contains p.goal) DProof.cut(p.goal, ds0.cuts) else p.right
          )) flatMap (_.fold(fd(_)(ds0), fp(_)(ds0)))
      }
    }

    def knowRHS[A[_]] = new {
      def apply[B, M](fd: Disproof[A[L]] => DerivationStep[B, M],
                      fp: Proof[A[L]] => DerivationStep[B, M])
                     (implicit k: Know[A, L, M], fn: FuncName): DerivationStep[B, M] = { ds0 =>
        k.byRHS(_lhs, ds0.m0) map
          (_.fold(
            d => d.left,
            p => if(ds0.cuts contains p.goal) DProof.cut(p.goal, ds0.cuts) else p.right
          )) flatMap (_.fold(fd(_)(ds0), fp(_)(ds0)))
      }
    }

    def knowValue[A] = new {
      def apply[B, M](fd: Disproof[A] => DerivationStep[B, M],
                      fp: Proof[A] => DerivationStep[B, M])
                     (implicit k: KnowValue[A, L, M], fn: FuncName): DerivationStep[B, M] = { ds0 =>
        k(_lhs, ds0.m0) map
          (a => Proof.fact(a).right[Disproof[A]]) map
          (_.fold(
            d => d.left,
            p => if(ds0.cuts contains p.goal) DProof.cut(p.goal, ds0.cuts) else p.right
          )) flatMap (_.fold(fd(_)(ds0), fp(_)(ds0)))
      }
    }
  }

  def allRanges[A, R, M](f: R => DerivationStep[A, M])
                        (implicit r: Ranges[R, M]): DerivationStep[A, M] = { ds0 =>
    r(ds0.m0) flatMap (rg => f(rg)(ds0))
  }

  implicit def resultP[A, M](p: Proof[A])(implicit t: Tell[A, M]): DerivationStep[A, M] = ds0 =>
    (p.right[Disproof[A]] -> (ds0 tell p.goal)).point[TrueStream]

  implicit def resultD[A, M](p: Disproof[A]): DerivationStep[A, M] = ds0 =>
    (p.left[Proof[A]] -> ds0).point[TrueStream]

  implicit def result[A, M](p: DProof[A])(implicit t: Tell[A, M]): DerivationStep[A, M] =
    p.fold(d => resultD(d), p => resultP(p))

  def lastModel[A, M](str: DerivationResults[A, M], m0: M): M =
    (str.foldLeft(m0) { case (_, (_, ds)) => ds.m0 }).value
}

trait DeriveImplicits {

  implicit def derive_lt[R, V, I]
  (implicit k: Know[LT, I, Model[R, V, I]])
  : Derive[LT[I], Model[R, V, I]] = DeriveOrdModel.`a < b -| ?`

  implicit def derive_lt_eq[R, V, I]
  (implicit kLtEq: Know[LT_EQ, I, Model[R, V, I]])
  : Derive[LT_EQ[I], Model[R, V, I]] = DeriveOrdModel.`a <= b -| ?`

  implicit def derive_eq[R, V, I]
  (implicit t: Tell[EQ[I], Model[R, V, I]]) // fixme: not sure why t is needed here but nowhere else
  : Derive[EQ[I], Model[R, V, I]] = DeriveOrdModel.`a = b -| ?`

  implicit def derive_not_eq[R, V, I]
  (implicit k: Know[NOT_EQ, I, Model[R, V, I]])
  : Derive[NOT_EQ[I], Model[R, V, I]] = DeriveOrdModel.`a != b -| ?`

  implicit def derive_at[R, V, I]: Derive[AT[I], Model[R, V, I]] = DeriveIndexModel.`a @ i -| ?`

  implicit def strand[R, V, I]
  : Derive[Strand[R], Model[R, V, I]] = DeriveStrandModel.`±r -| ?`

  implicit def derive_same_strand_as[R, V, I]
  : Derive[SameStrandAs[R], Model[R, V, I]] = DeriveStrandModel.`r±s -| ?`

  implicit def derive_different_strand_to[R, V, I]
  : Derive[DifferentStrandTo[R], Model[R, V, I]] = DeriveStrandModel.`r∓s -| ?`

}

trait DeriveLowPriorityImpicits {

  import Interpretation.InterpretationOps

  implicit def derive_usingInterpretation[A[_], R, V, I]
  (implicit
   in: Interpretation[A[V], A[I], Model[R, V, I]],
   d: Derive[A[I], Model[R, V, I]],
   fn: FuncName) = Derive[A[V], Model[R, V, I]] { a => ds0 =>
      val (a1, ds1) = ds0 interpretation a
      d(a1, ds1) map { case (p, ds) => p.fold(
      p => DProof.interpreted(a, p),
      p => DProof.interpreted(a, p)) -> ds }
   } (fn)

}
