package at.forsyte.apalache.tla.parser

import at.forsyte.apalache.tla.ir.Kind
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
    val spec = new XmlImporter().parse(xml)
    assert(0 == spec.modules.size)
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

    val spec = new XmlImporter().parse(xml)
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

    val spec = new XmlImporter().parse(xml)
    assert(1 == spec.modules.size)
    val module = spec.modules.head
    assert(1 == module.vars.size)
    val hr = module.vars.head
    assert("hr" == hr.uniqueName)
    assert(0 == hr.arity)
    assert(hr.origin.isDefined)
    assert(1 == hr.origin.get.level)
    assert(Kind.Var == hr.kind)

    assert("HourClock" == module.origin.filename)
    assert(1 == module.origin.locRange.start.colno)
    assert(1 == module.origin.locRange.start.lineno)
    assert(62 == module.origin.locRange.end.colno)
    assert(9 == module.origin.locRange.end.lineno)
  }
}
