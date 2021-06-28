# ADR-008: Apalache Exceptions

| author     | revision |
| ------------ | --------:|
| Jure Kukovec |    1 |

This ADR documents the various exception thrown in Apalache, and the circumstances that trigger them.

## 1. User input exceptions
Exceptions in this family are caused by incorrect input from the user. All of these exceptions should exit cleanly and should NOT report a stack trace.

### 1.1. Parser-level
Since we depend on Sany for parsing, Apalache rejects any syntax which Sany cannot parse.
If Sany produces an exception Apalache catches it and re-throws a class extending

```
ParserException
```

The exception should report the following details:

  * Location of at least one parser issue

### 1.2. Apalache-specific input exceptions
This category of exceptions deals with problems triggered by incorrect or incomplete information regarding Apalache inputs. Examples include:

  * Malformed config files
  * Incorrect or missing `OVERRIDE_`
  * Incorrect or missing `UNROLL_`
  * Problems with `--init/next/cinit/...`

Exceptions thrown in response to these issues should extend 

```
ApalacheInputException
```

The exceptions should report the following details:

  * If an input is missing: the name of the expected input 
  * If an input is incorrect: the way in which it is incorrect

### 1.3. Type-related exceptions
This category of exceptions deals with problems arising from the type-system used by Apalache. Examples include:

  * Missing or incorrect type annotations
  * Incompatibility of argument types and operator types
  
Exceptions thrown in response to these issues should extend 

```
TypeingException
```

The exceptions should report the following details:

  * If an annotation is missing: the declaration with the missing annotation and its location  
  * If the types of the arguments at a built-in operator application site are incompatible with the operator type: Both the computed and expected types, and the location of the application site 
  * If the types of the arguments at a user-defined operator application site are incompatible with the operator annotation: Both the computed and expected types, the operator declaration, and the location of the application site

### 1.4. Static-analysis exceptions
This category of exceptions deals with problems arising from the various static analysis passes performed by Apalache. Examples include:

  * Missing or incorrect variable assignments
  * Other analyses we might run in the future
  
Exceptions thrown in response to these issues should extend 

```
StaticAnalysisException
```

The exceptions should report the following details:

  * The location in the specification where the analysis failed and the expected result

### 1.5. Unsupported language exceptions
This category of exceptions deals with user input, which falls outside of the TLA+ fragment supported by Apalache. Examples include:

  * Unbounded quantification
  * (Unbounded) `CHOOSE`
  * `SelectSeq`
  * Fragments of community modules

Exceptions thrown in response to these issues should extend 

```
UnsupportedFeatureException
```

The exceptions should report the following details:

  * The location of the unsupported expression(s)

## 2. Tool failures
These exceptions are caused by bugs in Apalache. They are fatal and should throw with a stack trace.

### 2.1. Assumption violations
Whenever possible, it's recommended to test against the assumptions of a given pass/transformation. If the assumptions are violated, an

```
AssumptionViolationException
```

should be thrown. It should report the following details:

  * The assumption being violated
  * The pass/class/method in which the assumption is made

### 2.2. Pass/Transformation-specific exceptions
Depending on the pass/transformation, specialized exceptions may be thrown, to indicate some problem in either the pipeline, malformed input, missing or incomplete metadata or any other issue that cannot be circumvented. The exceptions should include a reasonable (concise) explanation and, whenever possible, source information for relevant expressions. 

## 3. Exception explanations
On their own, exceptions should include concise messages with all the relevant information components, outlined above. In addition to that, we should implement an advanced variant of `ExceptionAdapter`, called `ExceptionExplainer`, that is optionally enabled, if Apalache is invoked with the flag `--explain-exceptions` (alternatively, it could be on by default and disabled with a similar flag). 

The purpose of this class is to offer users a comprehensive explanation of the exceptions defined in Section 1. Whenever an exception is thrown, `ExceptionExplainer` should offer:

  * Inlined TLA+ code, in place of source location references
  * Examples of similar malformed inputs, if relevant
  * Suggestions on how to fix the exception
  * A link to the manual, explaining the cause of the exception

