package at.forsyte.apalache.tla.parser

import at.forsyte.apalache.tla.ir._
import org.junit.runner.RunWith
import org.scalatest.FunSuite
import org.scalatest.junit.JUnitRunner

/**
  * Tests for XmlImporter
  *
  * @see at.forsyte.apalache.tla.parser.XmlImporter
  *
  * @author konnov
  */
@RunWith(classOf[JUnitRunner])
class TestXmlImporterSuite extends FunSuite {
  test("empty spec") {
    val xml = <modules><context></context></modules>
    val (spec, errors) = new XmlImporter().parse(xml)
    assert(0 == spec.modules.size)
    assert(errors.isEmpty)
  }

  test("malformed xml") {
    val xml = <foo></foo>
    intercept[XmlImporterException] {
      new XmlImporter().parse(xml)
    }
  }

  test("one empty module") {
    val xml =
      <modules>
        <context/>
        <ModuleNode>
          <location>
            <column><begin>1</begin><end>62</end></column>
            <line><begin>1</begin><end>9</end></line>
            <filename>HC</filename>
          </location>
          <uniquename>HourClock</uniquename>
          <constants/>
          <variables/>
          <definitions/>
          <assumptions/>
          <theorems/>
        </ModuleNode>
      </modules>

    val (spec, errors) = new XmlImporter().parse(xml)
    assert(errors.isEmpty)
    assert(1 == spec.modules.size)
    val module = spec.modules.head
    assert("HourClock" == module.uniqueName)
    assert("HC" == module.origin.filename)
    assert(1 == module.origin.locRange.start.colno)
    assert(1 == module.origin.locRange.start.lineno)
    assert(62 == module.origin.locRange.end.colno)
    assert(9 == module.origin.locRange.end.lineno)
  }

  test("one variable") {
    val xml =
    <modules>
      <context>
        <entry>
          <UID>9</UID>
          <OpDeclNode>
            <location>
              <column><begin>5</begin><end>10</end></column>
              <line><begin>3</begin><end>4</end></line>
              <filename>HourClock</filename>
            </location>
            <level>1</level>
            <uniquename>hr</uniquename>
            <arity>0</arity>
            <kind>3</kind>
          </OpDeclNode>
        </entry>
      </context>
      <ModuleNode>
        <location>
          <column><begin>1</begin><end>62</end></column>
          <line><begin>1</begin><end>9</end></line>
          <filename>HourClock</filename>
        </location>
        <uniquename>HourClock</uniquename>
        <constants/>
        <variables>
          <OpDeclNodeRef><UID>9</UID></OpDeclNodeRef>
        </variables>
        <definitions/>
        <assumptions/>
        <theorems/>
      </ModuleNode>
    </modules>

    val (spec, errors) = new XmlImporter().parse(xml)
    assert(errors.isEmpty)
    assert(1 == spec.modules.size)
    val module = spec.modules.head
    assert(1 == module.variables.size)
    val hr = module.variables.head
    assert("hr" == hr.uniqueName)
    assert(0 == hr.arity)
    assert(1 == hr.origin.level)
    assert(Kind.Var == hr.kind)

    assert("HourClock" == module.origin.filename)
    assert(1 == module.origin.locRange.start.colno)
    assert(1 == module.origin.locRange.start.lineno)
    assert(62 == module.origin.locRange.end.colno)
    assert(9 == module.origin.locRange.end.lineno)
  }

  test("one definition") {
    val xml =
      <modules>
        <context>
          <!-- the equality operator -->
          <entry>
            <UID>4</UID>
            <BuiltInKind>
              <location>
                <column> <begin>0</begin> <end>0</end> </column>
                <line> <begin>0</begin> <end>0</end> </line>
                <filename>--TLA+ BUILTINS--</filename>
              </location>
              <level>0</level>
              <uniquename>=</uniquename>
              <arity>2</arity>
              <params>
                <leibnizparam>
                  <FormalParamNodeRef>
                    <UID>5</UID>
                  </FormalParamNodeRef>
                  <leibniz/>
                </leibnizparam>
                <leibnizparam>
                  <FormalParamNodeRef>
                    <UID>6</UID>
                  </FormalParamNodeRef>
                  <leibniz/>
                </leibnizparam>
              </params>
            </BuiltInKind>
          </entry>
          <entry>
            <UID>5</UID>
            <FormalParamNode>
              <uniquename>Formal_0</uniquename>
              <arity>0</arity>
            </FormalParamNode>
          </entry>
          <entry>
            <UID>6</UID>
            <FormalParamNode>
              <uniquename>Formal_1</uniquename>
              <arity>0</arity>
            </FormalParamNode>
          </entry>
          <!-- a user-defined operator -->
          <entry>
            <UID>234</UID>
            <UserDefinedOpKind>
              <location>
                <column><begin>1</begin><end>27</end></column>
                <line><begin>4</begin><end>4</end></line>
                <filename>HourClock</filename>
              </location>
              <level>1</level> <uniquename>HCini</uniquename> <arity>0</arity>
              <body>
                <OpApplNode>
                  <location> <column> <begin>12</begin> <end>27</end>
                    </column> <line> <begin>4</begin> <end>4</end> </line>
                    <filename>HourClock</filename>
                  </location>
                  <level>1</level>
                  <operator>
                    <BuiltInKindRef>
                      <UID>4</UID>
                    </BuiltInKindRef>
                  </operator>
                  <operands>
                    <OpApplNode>
                      <location> <column> <begin>12</begin> <end>13</end>
                        </column> <line> <begin>4</begin> <end>4</end> </line>
                        <filename>HourClock</filename>
                      </location>
                      <level>1</level>
                      <operator>
                        <OpDeclNodeRef>
                          <UID>9</UID>
                        </OpDeclNodeRef>
                      </operator>
                      <operands/>
                    </OpApplNode>
                    <OpApplNode>
                      <location> <column> <begin>12</begin> <end>13</end>
                        </column> <line> <begin>4</begin> <end>4</end> </line>
                        <filename>HourClock</filename>
                      </location>
                      <level>1</level>
                      <operator>
                        <OpDeclNodeRef>
                          <UID>9</UID>
                        </OpDeclNodeRef>
                      </operator>
                      <operands/>
                    </OpApplNode>
                  </operands>
                </OpApplNode>
              </body>
              <params/>
            </UserDefinedOpKind>
          </entry>

          <!-- a variable -->
          <entry>
            <UID>9</UID>
            <OpDeclNode>
              <location>
                <column><begin>5</begin><end>10</end></column>
                <line><begin>3</begin><end>4</end></line>
                <filename>HourClock</filename>
              </location>
              <level>1</level>
              <uniquename>hr</uniquename>
              <arity>0</arity>
              <kind>3</kind>
            </OpDeclNode>
          </entry>
        </context>
        <ModuleNode>
          <location>
            <column><begin>1</begin><end>62</end></column>
            <line><begin>1</begin><end>9</end></line>
            <filename>HourClock</filename>
          </location>
          <uniquename>HourClock</uniquename>
          <constants/>
          <variables/>
          <definitions>
            <UserDefinedOpKindRef>
              <UID>234</UID>
            </UserDefinedOpKindRef>
          </definitions>
          <assumptions/>
          <theorems/>
        </ModuleNode>
      </modules>

    val (spec, errors) = new XmlImporter().parse(xml)
    assert(errors.isEmpty)
    assert(1 == spec.modules.size)
    val module = spec.modules.head
    assert(1 == module.operators.size)

    // the standard things
    val op = module.operators.head
    assert(1 == op.origin.locRange.start.colno)
    assert(4 == op.origin.locRange.start.lineno)
    assert(27 == op.origin.locRange.end.colno)
    assert(4 == op.origin.locRange.end.lineno)
    assert(1 == op.origin.level)
    assert("HourClock" == op.origin.filename)

    // the parameters
    assert(op.params.isEmpty)

    // and now the body
    op.body match {
      case app: OpApply =>
        assert(4 == app.origin.locRange.start.lineno)
        assert(4 == app.origin.locRange.end.lineno)
        assert(12 == app.origin.locRange.start.colno)
        assert(27 == app.origin.locRange.end.colno)
        assert("HourClock" == app.origin.filename)
        assert(1 == app.origin.level)

        // the operator is actually a built-in operator
        app.oper match {
          case bop: BuiltinOp =>
            assert("=" == bop.uniqueName)
            assert("--TLA+ BUILTINS--" == bop.origin.filename)
            assert(0 == bop.origin.level)
            assert(2 == bop.params.size)
            val param0 = bop.params.head
            val param1 = bop.params.tail.head
            assert("Formal_0" == param0.uniqueName)
            assert(param0.isLeibniz)
            assert(0 == param0.arity)
            assert("Formal_1" == param1.uniqueName)
            assert(param1.isLeibniz)
            assert(0 == param1.arity)

          case _ =>
            fail("Expected BuiltinOp")
        }

        assert(2 == app.args.length)

        def isHr(operand: TlaNode): Unit = operand match {
          case opapp: OpApply =>
            assert(12 == opapp.origin.locRange.start.colno)
            assert(13 == opapp.origin.locRange.end.colno)
            assert(4 == opapp.origin.locRange.start.lineno)
            assert(4 == opapp.origin.locRange.end.lineno)
            assert("HourClock" == opapp.origin.filename)
            assert(1 == opapp.origin.level)

            opapp.oper match {
              case d: UserOpDecl =>
                assert("hr" == d.uniqueName)

              case _ =>
                fail("Expected hr")
            }

          case _ =>
            fail("Expected OpApply as the 0th operand")
        }

        isHr(app.args.head)
        isHr(app.args.tail.head)

      case _ =>
        fail("Expected OpApply")
    }
  }
}
