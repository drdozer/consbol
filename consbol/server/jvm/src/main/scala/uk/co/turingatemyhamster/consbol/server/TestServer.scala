package uk.co.turingatemyhamster.consbol.server


import akka.actor.ActorSystem
import akka.http.scaladsl._
import akka.http.scaladsl.marshalling._
import akka.http.scaladsl.model._
import akka.http.scaladsl.server._

import Directives._
import akka.stream.ActorMaterializer

import com.typesafe.config.ConfigFactory

import scalatags.Text.TypedTag

object TestServer extends App {
  implicit val system = ActorSystem()
  import system.dispatcher
  implicit val materializer = ActorMaterializer()

  lazy val config = ConfigFactory.load()

  implicit val ttMarshaller: ToResponseMarshaller[TypedTag[String]] =
    implicitly[ToResponseMarshaller[String]].wrap(MediaTypes.`text/html`)(_.render)

  val route: Route = {
    get {
      path("strand.html") {
        complete {
          StrandExample.strand
        }
      } ~
      pathPrefix("lib") {
        getFromResourceDirectory("lib")
      } ~
      getFromResourceDirectory("public")
    }
  }

  val serverConfig = config.getConfig("test-server")
  Http().bindAndHandle(route, serverConfig.getString("interface"), serverConfig.getInt("port"))

}
object StrandExample {

  import scalatags.Text.all._

  def strand = html(
    head(
      script(src := "/lib/jquery/jquery.min.js"),
      script(src := "/lib/jqtree/tree.jquery.js"),
      script(src := "/javascript/consbol-server-fastopt.js"),
      link(rel := "stylesheet", href := "/lib/jqtree/jqtree.css")
    ),
    body(
      h1("Strand inference"),
      div(id := "content"),
      script(`type` := "text/javascript")(
        """|DerivationApp().render(
           |  document.getElementById('content'));""".stripMargin
      )
    )
  )

}