// Test runner for Cubical Runtime tests (Scala)
package cubical.runtime

object Test extends App {
  println("Running Cubical Standard Tests (Scala Runtime)")
  println("============================================")
  Runtime.runStandardTests()
  if (Runtime.allTestsPass) {
    println("\nSUCCESS: All tests passed!")
    sys.exit(0)
  } else {
    println("\nFAIL: Some tests failed")
    sys.exit(1)
  }
}
