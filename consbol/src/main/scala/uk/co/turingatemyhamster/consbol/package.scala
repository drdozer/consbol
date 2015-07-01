package uk.co.turingatemyhamster

import scalaz.StreamT.{Yield, Step}
import scalaz.{Need, Name, StreamT}

/**
 * Created by nmrp3 on 30/06/15.
 */
package object consbol {

  type TrueStream[A] = StreamT[Need, A]

  def singleton[A](a: A): Step[A, StreamT[Need, A]] = {
    Yield(
      a,
      StreamT.empty)
  }
}
