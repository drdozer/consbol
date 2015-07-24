package uk.co.turingatemyhamster.consbol

import Unifier._
import Interpretation._
import monocle.macros._

@Lenses
case class Model[R, V, I](i: InterpModel[V, I],
                          ord: OrdModel[I],
                          index: IndexModel[I],
                          range: RangeModel[R, I],
                          str: StrandModel[R],
                          length: LengthModel[R])
{

  def merge(a: V, b: V)
           (implicit
            vi: InterpretationSingleton[V, I],
            unify: UnifyI[I],
            u: Unifier[I, Model[R, V, I]]): Model[R, V, I] =
  {
    if(a == b) {
      this
    } else {
      val (aI, i1) = i interpretation a
      val (bI, i2) = i1 interpretation b

      if(aI == bI) {
        this
      } else {
        val uI = unify(aI, bI)
        val i3 = i2.copy(v2i = i2.v2i + (a -> uI) + (b -> uI))
        copy(i = i3) unify (aI, bI, uI)
      }
    }
  }

}

object Model {
  def empty[R, V, I]: Model[R, V, I] = Model(
    i = InterpModel(),
    ord = OrdModel(),
    index = IndexModel(),
    range = RangeModel(),
    str = StrandModel(),
    length = LengthModel())
}

@Lenses
case class IndexModel[I](at: Map[I, Set[Int]] = Map.empty[I, Set[Int]],
                         suc: Set[(I, I)] = Set.empty[(I, I)])

@Lenses
case class InterpModel[V, I](v2i: Map[V, I] = Map.empty[V, I],
                             eq: Map[I, Set[V]] = Map.empty[I, Set[V]])

@Lenses
case class OrdModel[I](lt: Set[(I, I)] = Set.empty[(I, I)],
                       lt_eq: Set[(I, I)] = Set.empty[(I, I)],
                       not_eq: Set[(I, I)] = Set.empty[(I, I)])

@Lenses
case class StrandModel[R](strand: Map[R, Set[Orientation]] = Map.empty[R, Set[Orientation]],
                          same_strand_as: Set[(R, R)] = Set.empty[(R, R)],
                          different_strand_to: Set[(R, R)] = Set.empty[(R, R)])

@Lenses
case class LengthModel[R](length: Map[R, Set[Int]] = Map.empty[R, Set[Int]])

@Lenses
case class RangeModel[R, I](rangeAs: Map[R, Set[(I, I)]] = Map.empty[R, Set[(I, I)]])