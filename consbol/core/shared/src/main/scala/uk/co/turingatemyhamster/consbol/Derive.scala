package uk.co.turingatemyhamster.consbol

import uk.co.turingatemyhamster.consbol.util.FuncName

import scala.language.higherKinds
import scalaz._
import scalaz.Scalaz._

import Derive._
import Tell.TellOps

case class DerivationState[R, V, I](env: DeriveEnv[R, V, I],
                                    cuts: Set[Any] = Set.empty,
                                    refuted: Map[Set[Any], Set[Any]] = Map.empty,
                                    m0: Model[R, V, I])
{
  def withModel(m1: Model[R, V, I]): DerivationState[R, V, I] = copy(m0 = m1)
  def withCuts(cs: Set[Any]): DerivationState[R, V, I] = copy(cuts = cs)
  def withCut(c: Any): DerivationState[R, V, I] = copy(cuts = cuts + c)
}

trait DeriveLHS[A[_], T, R, V, I] {
  def apply(lhs: T): DerivationStep[A[T], R, V, I]
}

trait DeriveRHS[A[_], T, R, V, I] {
  def apply(rhs: T): DerivationStep[A[T], R, V, I]
}

trait Derive[A, R, V, I] {
  def apply(a: A, ds: DerivationState[R, V, I]): DerivationResults[A, R, V, I]
}

object Derive extends DeriveLowPriorityImpicits {

  type DProof[A] = Disproof[A] \/ Proof[A]
  type DerivationStep[A, R, V, I] = DerivationState[R, V, I] => DerivationResults[A, R, V, I]
  type DerivationResults[A, R, V, I] = TrueStream[(DProof[A], DerivationState[R, V, I])]

  def apply[A, R, V, I](d: A => DerivationStep[A, R, V, I])
                       (implicit fn: FuncName): Derive[A, R, V, I] = new Derive[A, R, V, I]
  {
    override def apply(a: A, ds0: DerivationState[R, V, I]): DerivationResults[A, R, V, I] =
      d(a)(ds0)
  }
}

trait DeriveLowPriorityImpicits {

  import Interpretation.InterpretationOps

  implicit def derive_usingInterpretation[A[_], R, V, I]
  (implicit
   in: Interpretation[A[V], A[I], DerivationState[R, V, I]],
   d: Derive[A[I], R, V, I],
   fn: FuncName) = Derive[A[V], R, V, I] { a => ds0 =>
      val (a1, ds1) = ds0 interpretation a
      d(a1, ds1) map { case (p, ds) => p.fold(
      p => DProof.interpreted(a, p),
      p => DProof.interpreted(a, p)) -> ds }
   } (fn)

}


trait DeriveDSL[R, V, I] {

  implicit def vi: InterpretationSingleton[V, I]
  implicit def unify: UnifyI[I]

  implicit def lhsFromRanges[A[_]]
  (implicit
   ops: BinOp[A, R],
   d: Derive[A[R], R, V, I],
   r: Atoms[R, Model[R, V, I]],
   t: Tell[A[R], DerivationState[R, V, I]],
   fn: FuncName)
  : DeriveLHS[A, R, R, V, I] = new DeriveLHS[A, R, R, V, I] {

    override def apply(lhs: R): DerivationStep[A[R], R, V, I] = {
      all[A, R] { rhs =>
        ops.recompose(lhs -> rhs) derive (d => d, p => p)
      }
    }
  }

  implicit def lhsFromIndexes[A[_]]
  (implicit
   ops: BinOp[A, I],
   d: Derive[A[I], R, V, I],
   r: Atoms[I, Model[R, V, I]],
   t: Tell[A[I], DerivationState[R, V, I]],
   fn: FuncName)
  : DeriveLHS[A, I, R, V, I] = new DeriveLHS[A, I, R, V, I] {
    override def apply(lhs: I): DerivationStep[A[I], R, V, I] = {
      all[A, I] { rhs =>
        ops.recompose(lhs -> rhs) derive (d => d, p => p)
      }
    }
  }

  implicit def rhsFromRanges[A[_]]
  (implicit
   ops: BinOp[A, R],
   d: Derive[A[R], R, V, I],
   r: Atoms[R, Model[R, V, I]],
   t: Tell[A[R], DerivationState[R, V, I]],
   fn: FuncName)
  : DeriveRHS[A, R, R, V, I] = new DeriveRHS[A, R, R, V, I] {

    override def apply(rhs: R): DerivationStep[A[R], R, V, I] = {
      all[A, R] { lhs =>
        ops.recompose(lhs -> rhs) derive (d => d, p => p)
      }
    }
  }

  implicit def rhsFromIndexes[A[_]]
  (implicit
   ops: BinOp[A, I],
   d: Derive[A[I], R, V, I],
   r: Atoms[I, Model[R, V, I]],
   t: Tell[A[I], DerivationState[R, V, I]],
   fn: FuncName)
  : DeriveRHS[A, I, R, V, I] = new DeriveRHS[A, I, R, V, I] {
    override def apply(rhs: I): DerivationStep[A[I], R, V, I] = {
      all[A, I] { lhs =>
        ops.recompose(lhs -> rhs) derive (d => d, p => p)
      }
    }
  }

  implicit class TrueStreamOps[A](val _s: Derive[A, R, V, I]) {
    def ||(_t: Derive[A, R, V, I]) = new Derive[A, R, V, I] {
      override def apply(a: A, ds0: DerivationState[R, V, I]): DerivationResults[A, R, V, I] = {
        val k1 = _s(a, ds0)

        def lazyProcess(h: (DProof[A], DerivationState[R, V, I]),
                        t: DerivationResults[A, R, V, I]): DerivationResults[A, R, V, I] = StreamT(t.uncons map {
          case None =>
            StreamT.Yield(h, _t(a, h._2))
          case Some((hh, tt)) =>
            StreamT.Yield(h, lazyProcess(hh, tt))
        })

        k1.uncons map {
          case None =>
            _t(a, ds0)
          case Some((h, t)) =>
            lazyProcess(h, t)
        } value
      }
    }

    def log(implicit fn: FuncName): Derive[A, R, V, I] = Derive[A, R, V, I] { a => ds0 =>
        println(s"${" " * ds0.cuts.size}${fn.name} [$a] ${ds0.cuts contains a} ${ds0.cuts} ${ds0.refuted}")
        _s(a, ds0)
    }
  }

  implicit class TrueStreamOps0[O[_], T](val _s: Derive[O[T], R, V, I]) {
    def swap(implicit b: BinOp[O, T], fn: FuncName): Derive[O[T], R, V, I] = Derive[O[T], R, V, I] { a => ds0 =>
        val (l, r) = b.decompose(a)
        val i = b.recompose(r, l)
        _s(i, ds0)
    }

    def sym(implicit b: BinOp[O, T], fn: FuncName): Derive[O[T], R, V, I] =
      _s || _s.swap
  }

  def guard[A](d: Derive[A, R, V, I])(implicit fn: FuncName) = Derive[A, R, V, I] { a => ds0 =>
      if(ds0.cuts contains a)
      {
//        println(s"guard $a ${ds0.cuts} !")
        (DProof.cut(a, ds0.cuts) -> ds0).point[TrueStream]
      }
      else
      {
//        println(s"guard $a ${ds0.cuts}")
        d(a, ds0 withCut a) map (ds => (DProof1(a, ds._1), ds._2 withCuts ds0.cuts))
      }
  }

  def withEnv[A](f: DeriveEnv[R, V, I] => A => DerivationStep[A, R, V, I])
                (implicit fn: FuncName): Derive[A, R, V, I] = Derive { a => ds0 =>
    f(ds0.env)(a)(ds0)
  }

  def newEnv[A](env: DeriveEnv[R, V, I])(fp: Proof[A] => DerivationStep[A, R, V, I]): Proof[A] => DerivationStep[A, R, V, I] = p => ds0 =>
    fp(p)(ds0.copy(env = env)) map { case (dp, ds1) => (dp, ds1.copy(env = ds0.env)) }

  def known[A[_], T]
  (implicit k: Know[A, T, DerivationState[R, V, I]], fn: FuncName) = Derive[A[T], R, V, I] { a => ds0 =>
      k(a, ds0) map
         (_ -> ds0)
  }

  def onlyIf[A, B](p: Boolean)(f: DerivationStep[B, R, V, I])
  : DerivationStep[B, R, V, I] =
    if(p)
      f
    else
      _ => StreamT.empty

  def derivationStep[A, B](rs: DerivationResults[A, R, V, I],
                           fd: Disproof[A] => DerivationStep[B, R, V, I],
                           fp: Proof[A] => DerivationStep[B, R, V, I])
                          (implicit fn: FuncName)
  : DerivationResults[B, R, V, I] = rs flatMap {
    case (s1O, ds1) =>
      s1O fold(
        d => d.left,
        p => if(ds1.cuts contains p.goal) DProof.cut(p.goal, ds1.cuts) else p.right
        ) fold(
        d => fd(d)(ds1),
        p => fp(p)(ds1))
  }

  implicit class AssertionOps[A](val _a: A) {
    def derive[B](fd: Disproof[A] => DerivationStep[B, R, V, I],
                  fp: Proof[A] => DerivationStep[B, R, V, I])
                 (implicit d: Derive[A, R, V, I], fn: FuncName): DerivationStep[B, R, V, I] = ds0 =>
      derivationStep(d(_a, ds0), fd, fp)
  }

  implicit class ValueOps[L](val _lhs: L) {
    def deriveLHS[A[_]] = new {
      def apply[B](fd: Disproof[A[L]] => DerivationStep[B, R, V, I],
                   fp: Proof[A[L]] => DerivationStep[B, R, V, I])
                  (implicit d: DeriveLHS[A, L, R, V, I], fn: FuncName): DerivationStep[B, R, V, I] = ds0 =>
        derivationStep(d(_lhs)(ds0), fd, fp)
    }

    def deriveRHS[A[_]] = new {
      def apply[B](fd: Disproof[A[L]] => DerivationStep[B, R, V, I],
                   fp: Proof[A[L]] => DerivationStep[B, R, V, I])
                  (implicit d: DeriveRHS[A, L, R, V, I], fn: FuncName): DerivationStep[B, R, V, I] = ds0 =>
        derivationStep(d(_lhs)(ds0), fd, fp)
    }

    def knowLHS[A[_]] = new {
      def apply[B](fd: Disproof[A[L]] => DerivationStep[B, R, V, I],
                   fp: Proof[A[L]] => DerivationStep[B, R, V, I])
                  (implicit k: Know[A, L, Model[R, V, I]], fn: FuncName): DerivationStep[B, R, V, I] = { ds0 =>
        k.byLHS(_lhs, ds0.m0) map
          (_.fold(
            d => d.left,
            p => if(ds0.cuts contains p.goal) DProof.cut(p.goal, ds0.cuts) else p.right
          )) flatMap (_.fold(fd(_)(ds0), fp(_)(ds0)))
      }
    }

    def knowRHS[A[_]] = new {
      def apply[B](fd: Disproof[A[L]] => DerivationStep[B, R, V, I],
                   fp: Proof[A[L]] => DerivationStep[B, R, V, I])
                  (implicit k: Know[A, L, Model[R, V, I]], fn: FuncName): DerivationStep[B, R, V, I] = { ds0 =>
        k.byRHS(_lhs, ds0.m0) map
          (_.fold(
            d => d.left,
            p => if(ds0.cuts contains p.goal) DProof.cut(p.goal, ds0.cuts) else p.right
          )) flatMap (_.fold(fd(_)(ds0), fp(_)(ds0)))
      }
    }

    def knowValue[A] = new {
      def apply[B](fd: Disproof[A] => DerivationStep[B, R, V, I],
                   fp: Proof[A] => DerivationStep[B, R, V, I])
                  (implicit k: KnowValue[A, L, Model[R, V, I]], fn: FuncName): DerivationStep[B, R, V, I] = { ds0 =>
        k(_lhs, ds0.m0) map
          (a => Proof.fact(a).right[Disproof[A]]) map
          (_.fold(
            d => d.left,
            p => if(ds0.cuts contains p.goal) DProof.cut(p.goal, ds0.cuts) else p.right
          )) flatMap (_.fold(fd(_)(ds0), fp(_)(ds0)))
      }
    }
  }

  def all[A[_], T](f: T => DerivationStep[A[T], R, V, I])
            (implicit r: Atoms[T, Model[R, V, I]]): DerivationStep[A[T], R, V, I] = { ds0 =>
    r(ds0.m0) flatMap (rg => f(rg)(ds0))
  }

  implicit def resultP[A](p: Proof[A])(implicit t: Tell[A, DerivationState[R, V, I]]): DerivationStep[A, R, V, I] = ds0 =>
    (p.right[Disproof[A]] -> (ds0 tell p.goal)).point[TrueStream]

  implicit def resultD[A](p: Disproof[A]): DerivationStep[A, R, V, I] = ds0 =>
    (p.left[Proof[A]] -> ds0).point[TrueStream]

  implicit def result[A](p: DProof[A])(implicit t: Tell[A, DerivationState[R, V, I]]): DerivationStep[A, R, V, I] =
    p.fold(d => resultD(d), p => resultP(p))

  implicit class DeriveEnvOps(_env: DeriveEnv[R, V, I]) {
    def without[A](dropList: List[Derive[A, R, V, I]])
                  (implicit w: DeriveEnvWithout[A, R, V, I]): DeriveEnv[R, V, I] =
      w(_env, dropList)
  }
}

trait DeriveEnvWithout[A, R, V, I] {
  def apply(env: DeriveEnv[R, V, I], dropList: List[Derive[A, R, V, I]]): DeriveEnv[R, V, I]
}

object DeriveEnvWithout {
  implicit def withoutSameStrandAs[R, V, I]: DeriveEnvWithout[SameStrandAs[R], R, V, I] =
    new DeriveEnvWithout[SameStrandAs[R], R, V, I] {
      override def apply(env: DeriveEnv[R, V, I], dropList: List[Derive[SameStrandAs[R], R, V, I]]): DeriveEnv[R, V, I] =
        env.copy(derives_SameStrandAs = env.derives_SameStrandAs diff dropList)
    }

  implicit def withoutDifferentStrandTo[R, V, I]: DeriveEnvWithout[DifferentStrandTo[R], R, V, I] =
    new DeriveEnvWithout[DifferentStrandTo[R], R, V, I] {
      override def apply(env: DeriveEnv[R, V, I], dropList: List[Derive[DifferentStrandTo[R], R, V, I]]): DeriveEnv[R, V, I] =
        env.copy(derives_DifferentStrandTo = env.derives_DifferentStrandTo diff dropList)
    }
}

trait DeriveRules[R, V, I]
  extends OrdDeriveRules[R, V, I]
  with IndexDeriveRules[R, V, I]
  with StrandDeriveRules[R, V, I]
  with DeriveDSL[R, V, I]

object DeriveRules {
  def apply[R, V, I](implicit _vi: InterpretationSingleton[V, I], _unify: UnifyI[I]): DeriveRules[R, V, I] =
    new DeriveRules[R, V, I]
    {
      override implicit final def vi: InterpretationSingleton[V, I] = _vi

      override implicit final def unify: UnifyI[I] = _unify
    }
}

trait DeriveEnvBase[R, V, I] {
  val rules: DeriveDSL[R, V, I]
}

case class DeriveEnv[R, V, I](rules: DeriveRules[R, V, I],
                              derives_LT: List[Derive[LT[I], R, V, I]],
                              derives_LT_EQ: List[Derive[LT_EQ[I], R, V, I]],
                              derives_EQ: List[Derive[EQ[I], R, V, I]],
                              derives_NOT_EQ: List[Derive[NOT_EQ[I], R, V, I]],
                              derives_AT: List[Derive[AT[I], R, V, I]],
                              derives_Suc: List[Derive[Suc[I], R, V, I]],
                              derives_SameStrandAs: List[Derive[SameStrandAs[R], R, V, I]],
                              derives_DifferentStrandTo: List[Derive[DifferentStrandTo[R], R, V, I]],
                              derives_Strand: List[Derive[Strand[R], R, V, I]])
  extends OrdDeriveEnv[R, V, I]
  with IndexDeriveEnv[R, V, I]
  with StrandDeriveEnv[R, V, I]
  with DeriveEnvBase[R, V, I]

object DeriveEnv {
  def apply[R, V, I](rules: DeriveRules[R, V, I]) = new DeriveEnv[R, V, I](
    rules = rules,
    derives_LT =
      rules.`a < b -| k(a < b)` ::
        rules.`a < b -| a @ i, b @ j, i < j` ::
        rules.`a < b -| suc(a, b)` ::
        rules.`a < c -| a < b, b < c` ::
        rules.`a < c -| a < b, b <= c` ::
        rules.`a < c -| a <= b, b < c` ::
        Nil,
    derives_LT_EQ =
      rules.`a <= b -| k(a <= b)` ::
        rules.`a <= b -| a @ i, b @ j, i <= j` ::
        rules.`a <= b -| a < b` ::
        rules.`a <= b -| ∃c: b suc c. a < c` ::
        rules.`a <= c -| a <= b, b <= c` ::
        Nil,
    derives_EQ =
      rules.`a = b -| a @ i, b @ j, i = j` ::
        rules.`a = b -| a <=b, b <= a` ::
        rules.`a = b -| ∃c: a suc c, b suc c` ::
        rules.`a = b -| ∃c: c suc a, c suc b` ::
        Nil,
    derives_NOT_EQ =
      rules.`a != b -| k(a != b)` ::
        rules.`a != b -| a @ i, b @ j, i != j` ::
        rules.`a != b -| a < b` ::
        rules.`a != b -| b < a` ::
        Nil,

    derives_AT =
      rules.`a @ i -| k(a @ i)` ::
        rules.`a @ i -| ∃b: k(a suc b), b @ (i+1)` ::
        rules.`a @ i -| ∃b: k(b suc a), b @ (i-1)` ::
        Nil,
    derives_Suc =
      rules.`a suc b -| k(a suc b)` ::
        rules.`a suc b -| a @ i, b @ j | i+1=j` ::
        Nil,

    derives_SameStrandAs =
      rules.`r±s -| k(r±s) or k(s±r)` ::
        rules.`r±s -| +r, +s` ::
        rules.`r±s -| -r, -s` ::
        rules.`r±s -| ∃t: k(r±t). t±s` ::
        rules.`r±s -| ∃t: k(r∓t). t∓s` ::
        rules.`r±s -| ∃t: k(t±r). t±s` ::
        rules.`r±s -| ∃t: k(t∓r). t∓s` ::
        Nil,
    derives_DifferentStrandTo =
      rules.`r∓s -| k(r∓s) or k(s∓r)` ::
        rules.`r∓s -| +r, -s` ::
        rules.`r∓s -| -r, +s` ::
        rules.`r∓s -| ∃t: k(r∓t). t±s` ::
        rules.`r∓s -| ∃t: k(r±t). t∓s` ::
        rules.`r∓s -| ∃t: k(t∓r). t±s` ::
        rules.`r∓s -| ∃t: k(t±r). t∓s` ::
        Nil,
    derives_Strand =
      rules.`±r -| k(±r)` ::
        rules.`±r -| ∃s: ±s. r±s` ::
        rules.`±r -| ∃s: ∓s, r∓s` ::
        Nil
  )
}
