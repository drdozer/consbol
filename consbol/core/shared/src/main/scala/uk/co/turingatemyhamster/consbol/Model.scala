package uk.co.turingatemyhamster.consbol

import Unifier._
import Interpretation._

/**
 * Created by nmrp3 on 28/06/15.
 */
case class Model[R, V, I](i: InterpModel[V, I],
                          ord: OrdModel[I],
                          index: IndexModel[I],
                          range: RangeModel[R, V],
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

case class IndexModel[I](at: Map[I, Set[Int]] = Map.empty[I, Set[Int]],
                         suc: Set[(I, I)] = Set.empty[(I, I)])

case class InterpModel[V, I](v2i: Map[V, I] = Map.empty[V, I],
                             eq: Map[I, Set[V]] = Map.empty[I, Set[V]])

case class OrdModel[I](lt: Set[(I, I)] = Set.empty[(I, I)],
                       lt_eq: Set[(I, I)] = Set.empty[(I, I)],
                       not_eq: Set[(I, I)] = Set.empty[(I, I)])

case class StrandModel[R](strand: Map[R, Set[Orientation]] = Map.empty[R, Set[Orientation]],
                          same_strand_as: Set[(R, R)] = Set.empty[(R, R)],
                          different_strand_to: Set[(R, R)] = Set.empty[(R, R)])

case class LengthModel[R](length: Map[R, Set[Int]] = Map.empty[R, Set[Int]])

case class RangeModel[R, V](rangeAs: Map[R, Set[(V, V)]] = Map.empty[R, Set[(V, V)]])