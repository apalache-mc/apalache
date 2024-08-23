package at.forsyte.apalache.io.lir

import at.forsyte.apalache.tla.lir._
import at.forsyte.apalache.tla.types.tla._
import org.junit.runner.RunWith
import org.scalatest.funsuite.AnyFunSuite
import org.scalatestplus.junit.JUnitRunner

@RunWith(classOf[JUnitRunner])
class TestCounterexampleWriter extends AnyFunSuite with TestCounterexampleWriterBase {
  test("single state") {
    compare(
        "tla",
        new TlaModule("test", List()),
        gt(name("x", IntT1), int(1)),
        List(
            ("", Map()),
            ("", Map("x" -> int(2))),
        ),
        """---------------------------- MODULE counterexample ----------------------------
        |
        |EXTENDS test
        |
        |(* Constant initialization state *)
        |ConstInit == TRUE
        |
        |(* Initial state *)
        |State0 == x = 2
        |
        |(* The following formula holds true in the last state and violates the invariant *)
        |InvariantViolation == x > 1
        |
        |================================================================================
        |(* Created by Apalache on DATETIME *)
        |(* https://github.com/informalsystems/apalache *)
        |""".stripMargin,
    )
  }

  test("two steps") {
    compare(
        "tla",
        new TlaModule("test", List()),
        gt(name("x", IntT1), int(1)),
        List(
            ("", Map()),
            ("", Map("x" -> int(0))),
            ("Trans1", Map("x" -> int(1))),
            ("Trans2", Map("x" -> int(2))),
        ),
        """---------------------------- MODULE counterexample ----------------------------
          |
          |EXTENDS test
          |
          |(* Constant initialization state *)
          |ConstInit == TRUE
          |
          |(* Initial state *)
          |State0 == x = 0
          |
          |(* Transition Trans1 to State1 *)
          |State1 == x = 1
          |
          |(* Transition Trans2 to State2 *)
          |State2 == x = 2
          |
          |(* The following formula holds true in the last state and violates the invariant *)
          |InvariantViolation == x > 1
          |
          |================================================================================
          |(* Created by Apalache on DATETIME *)
          |(* https://github.com/informalsystems/apalache *)
          |""".stripMargin,
    )
  }

  test("two steps with conjunction") {
    compare(
        "tla",
        new TlaModule("test", List()),
        and(gt(name("x", IntT1), int(1)), eql(name("y", IntT1), int(10))),
        List(
            ("", Map()),
            ("", Map("x" -> int(0), "y" -> int(8))),
            ("Trans1", Map("x" -> int(1), "y" -> int(9))),
            ("Trans2", Map("x" -> int(2), "y" -> int(10))),
        ),
        """---------------------------- MODULE counterexample ----------------------------
        |
        |EXTENDS test
        |
        |(* Constant initialization state *)
        |ConstInit == TRUE
        |
        |(* Initial state *)
        |State0 == x = 0 /\ y = 8
        |
        |(* Transition Trans1 to State1 *)
        |State1 == x = 1 /\ y = 9
        |
        |(* Transition Trans2 to State2 *)
        |State2 == x = 2 /\ y = 10
        |
        |(* The following formula holds true in the last state and violates the invariant *)
        |InvariantViolation == x > 1 /\ y = 10
        |
        |================================================================================
        |(* Created by Apalache on DATETIME *)
        |(* https://github.com/informalsystems/apalache *)
        |""".stripMargin,
    )
  }

  test("TLC single state") {
    compare(
        "tlc",
        new TlaModule("test", List()),
        gt(name("x", IntT1), int(1)),
        List(
            ("", Map()),
            ("", Map("x" -> int(2))),
        ),
        """@!@!@STARTMSG 2262:0 @!@!@
        |Created by Apalache on DATETIME
        |@!@!@ENDMSG 2262 @!@!@
        |@!@!@STARTMSG 2110:1 @!@!@
        |Invariant is violated.
        |@!@!@ENDMSG 2110 @!@!@
        |@!@!@STARTMSG 2121:1 @!@!@
        |The behavior up to this point is:
        |@!@!@ENDMSG 2121 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |1: <Initial predicate>
        |x = 2
        |
        |@!@!@ENDMSG 2217 @!@!@
        |""".stripMargin,
    )
  }

  test("TLC two steps") {
    compare(
        "tlc",
        new TlaModule("test", List()),
        gt(name("x", IntT1), int(1)),
        List(
            ("", Map()),
            ("", Map("x" -> int(0))),
            ("Next", Map("x" -> int(1))),
            ("Next", Map("x" -> int(2))),
        ),
        """@!@!@STARTMSG 2262:0 @!@!@
        |Created by Apalache on DATETIME
        |@!@!@ENDMSG 2262 @!@!@
        |@!@!@STARTMSG 2110:1 @!@!@
        |Invariant is violated.
        |@!@!@ENDMSG 2110 @!@!@
        |@!@!@STARTMSG 2121:1 @!@!@
        |The behavior up to this point is:
        |@!@!@ENDMSG 2121 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |1: <Initial predicate>
        |x = 0
        |
        |@!@!@ENDMSG 2217 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |2: <Next>
        |x = 1
        |
        |@!@!@ENDMSG 2217 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |3: <Next>
        |x = 2
        |
        |@!@!@ENDMSG 2217 @!@!@
        |""".stripMargin,
    )
  }

  test("TLC two steps with conjunction") {
    compare(
        "tlc",
        new TlaModule("test", List()),
        and(gt(name("x", IntT1), int(1)), eql(name("y", IntT1), int(10))),
        List(
            ("", Map()),
            ("", Map("x" -> int(0), "y" -> int(8))),
            ("Trans1", Map("x" -> int(1), "y" -> int(9))),
            ("Trans2", Map("x" -> int(2), "y" -> int(10))),
        ),
        """@!@!@STARTMSG 2262:0 @!@!@
        |Created by Apalache on DATETIME
        |@!@!@ENDMSG 2262 @!@!@
        |@!@!@STARTMSG 2110:1 @!@!@
        |Invariant is violated.
        |@!@!@ENDMSG 2110 @!@!@
        |@!@!@STARTMSG 2121:1 @!@!@
        |The behavior up to this point is:
        |@!@!@ENDMSG 2121 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |1: <Initial predicate>
        |/\ x = 0
        |/\ y = 8
        |
        |@!@!@ENDMSG 2217 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |2: <Next>
        |/\ x = 1
        |/\ y = 9
        |
        |@!@!@ENDMSG 2217 @!@!@
        |@!@!@STARTMSG 2217:4 @!@!@
        |3: <Next>
        |/\ x = 2
        |/\ y = 10
        |
        |@!@!@ENDMSG 2217 @!@!@
        |""".stripMargin,
    )
  }

  test("JSON single state") {
    compare(
        "json",
        new TlaModule("test", List()),
        gt(name("x", IntT1), int(1)),
        List(
            ("", Map()),
            ("", Map("x" -> int(2))),
        ),
        """{
          |  "name": "ApalacheIR",
          |  "version": "1.0",
          |  "description": "https://apalache-mc.org/docs/adr/005adr-json.html",
          |  "modules": [
          |    {
          |      "kind": "TlaModule",
          |      "name": "counterexample",
          |      "declarations": [
          |        {
          |          "type": "(() => Bool)",
          |          "kind": "TlaOperDecl",
          |          "name": "ConstInit",
          |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "ValEx",
        |            "value": {
        |              "kind": "TlaBool",
        |              "value": true
        |            }
        |          }
        |        },
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "State0",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "OperEx",
        |            "oper": "AND",
        |            "args": [
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "x"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 2
        |                    }
        |                  }
        |                ]
        |              }
        |            ]
        |          }
        |        },
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "InvariantViolation",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "OperEx",
        |            "oper": "GT",
        |            "args": [
        |              {
        |                "type": "Int",
        |                "kind": "NameEx",
        |                "name": "x"
        |              },
        |              {
        |                "type": "Int",
        |                "kind": "ValEx",
        |                "value": {
        |                  "kind": "TlaInt",
        |                  "value": 1
        |                }
        |              }
        |            ]
        |          }
        |        }
        |      ]
        |    }
        |  ]
        |}""".stripMargin,
    )
  }

  test("JSON two steps") {
    compare(
        "json",
        new TlaModule("test", List()),
        gt(name("x", IntT1), int(1)),
        List(
            ("", Map()),
            ("", Map("x" -> int(0))),
            ("Trans1", Map("x" -> int(1))),
            ("Trans2", Map("x" -> int(2))),
        ),
        """{
        |  "name": "ApalacheIR",
        |  "version": "1.0",
        |  "description": "https://apalache-mc.org/docs/adr/005adr-json.html",
        |  "modules": [
        |    {
        |      "kind": "TlaModule",
        |      "name": "counterexample",
        |      "declarations": [
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "ConstInit",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "ValEx",
        |            "value": {
        |              "kind": "TlaBool",
        |              "value": true
        |            }
        |          }
        |        },
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "State0",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "OperEx",
        |            "oper": "AND",
        |            "args": [
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "x"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 0
        |                    }
        |                  }
        |                ]
        |              }
        |            ]
        |          }
        |        },
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "State1",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "OperEx",
        |            "oper": "AND",
        |            "args": [
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "x"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 1
        |                    }
        |                  }
        |                ]
        |              }
        |            ]
        |          }
        |        },
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "State2",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "OperEx",
        |            "oper": "AND",
        |            "args": [
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "x"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 2
        |                    }
        |                  }
        |                ]
        |              }
        |            ]
        |          }
        |        },
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "InvariantViolation",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "OperEx",
        |            "oper": "GT",
        |            "args": [
        |              {
        |                "type": "Int",
        |                "kind": "NameEx",
        |                "name": "x"
        |              },
        |              {
        |                "type": "Int",
        |                "kind": "ValEx",
        |                "value": {
        |                  "kind": "TlaInt",
        |                  "value": 1
        |                }
        |              }
        |            ]
        |          }
        |        }
        |      ]
        |    }
        |  ]
        |}""".stripMargin,
    )
  }

  test("JSON two steps with conjunction") {
    compare(
        "json",
        new TlaModule("test", List()),
        and(gt(name("x", IntT1), int(1)), eql(name("y", IntT1), int(10))),
        List(
            ("", Map()),
            ("", Map("x" -> int(0), "y" -> int(8))),
            ("Trans1", Map("x" -> int(1), "y" -> int(9))),
            ("Trans2", Map("x" -> int(2), "y" -> int(10))),
        ),
        """{
        |  "name": "ApalacheIR",
        |  "version": "1.0",
        |  "description": "https://apalache-mc.org/docs/adr/005adr-json.html",
        |  "modules": [
        |    {
        |      "kind": "TlaModule",
        |      "name": "counterexample",
        |      "declarations": [
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "ConstInit",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "ValEx",
        |            "value": {
        |              "kind": "TlaBool",
        |              "value": true
        |            }
        |          }
        |        },
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "State0",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "OperEx",
        |            "oper": "AND",
        |            "args": [
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "x"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 0
        |                    }
        |                  }
        |                ]
        |              },
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "y"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 8
        |                    }
        |                  }
        |                ]
        |              }
        |            ]
        |          }
        |        },
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "State1",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "OperEx",
        |            "oper": "AND",
        |            "args": [
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "x"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 1
        |                    }
        |                  }
        |                ]
        |              },
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "y"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 9
        |                    }
        |                  }
        |                ]
        |              }
        |            ]
        |          }
        |        },
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "State2",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "OperEx",
        |            "oper": "AND",
        |            "args": [
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "x"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 2
        |                    }
        |                  }
        |                ]
        |              },
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "y"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 10
        |                    }
        |                  }
        |                ]
        |              }
        |            ]
        |          }
        |        },
        |        {
        |          "type": "(() => Bool)",
        |          "kind": "TlaOperDecl",
        |          "name": "InvariantViolation",
        |          "formalParams": [],
        |          "isRecursive": false,
        |          "body": {
        |            "type": "Bool",
        |            "kind": "OperEx",
        |            "oper": "AND",
        |            "args": [
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "GT",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "x"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 1
        |                    }
        |                  }
        |                ]
        |              },
        |              {
        |                "type": "Bool",
        |                "kind": "OperEx",
        |                "oper": "EQ",
        |                "args": [
        |                  {
        |                    "type": "Int",
        |                    "kind": "NameEx",
        |                    "name": "y"
        |                  },
        |                  {
        |                    "type": "Int",
        |                    "kind": "ValEx",
        |                    "value": {
        |                      "kind": "TlaInt",
        |                      "value": 10
        |                    }
        |                  }
        |                ]
        |              }
        |            ]
        |          }
        |        }
        |      ]
        |    }
        |  ]
        |}""".stripMargin,
    )
  }
}
