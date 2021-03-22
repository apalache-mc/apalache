# ADR-005: JSON Serialization Format

| author       | revision |
| ------------ | --------:|
| Jure Kukovec |        1 |

This ADR documents our decision on serializing the Apalache internal representation (IR) as JSON.
The purpose of introducing such a serialization is to expose the internal representation in a standardized format, which can be used for persistent storage, or for analysis by third-party tools in the future.

## 1. Serializable classes

The following classes are serializable:
1. TLA+ expressions `TlaEx` and subclasses thereof:
  1. Named expressions `NameEx`
  1. Literal values `ValEx` for the following literals:
    1. Integers `TlaInt`
    1. Strings `TlaStr`
    1. Booleans `TlaBool`
    1. Decimals `TlaDecimal`
  1. Operator expressions `OperEx`
  1. LET-IN expressions `LetInEx`
1. TLA+ declarations `TlaDecl` and subclasses thereof:
  1. Variable declarations `TlaVarDecl`
  1. Constant declarations `TlaConstDecl`
  1. Operator declarations `TlaOperDecl`
  1. Assumption declarations `TlaAssumeDecl`
  1. Theorem declarations `TlaTheoremDecl`
1. TLA+ modules `TlaModule`

## 2. Disambiguation field

Every serialization will contain a disambiguation field, named `kind`. This field holds the name of the class being serialized. For example, the serialization of a `NameEx` will have the shape
```
{
  kind: "NameEx"
  ...
}
```

## 3. Serializing typed entities

Serializations of typed entities will have an additional field named `type`, containing the type of the expression (see [ADR-002][], [ADR-004][] for a description of our type system and the syntax for types-as-string-annotations respectively). For example, the integer literal `1` is represented by a `ValEx`, which has type `Int` and is serialized as follows:
```
{
  kind: "NameEx"
  type: "Int"
  ...
}
```

## 4. Serialization rules

The goal of the serialization is for the JSON structure to mimic the internal representation as closely as possible, for ease of deserialization. 
Concretely, whenever a class declares a field `fld: T`, its serialization also contains a field named `fld`, containing the serialization of the field value.
For example, if `TlaConstDecl` declares a `name: String` field, its JSON serialization will have a `name` field as well, containing the name string.

If a class field has the type `Traversable[T]`, for some `T`, the corresponding JSON entry is a list containing serializations of the individual arguments. For example, `OperEx` is variadic and declares `args: TlaEx*`, so its serialization has an `args` field containing a (possibly empty) list.

As a running example, take the expression `1 + 1`, represented with the correct type annotations as 
```
OperEx( 
  oper = TlaArithOper.plus, 
  args = Seq( 
    ValEx( TlaInt( 1 ) )( typeTag = Typed( IntT1() ) ), 
    ValEx( TlaInt( 1 ) )( typeTag = Typed( IntT1() ) )
    ) 
  )( typeTag = Typed( IntT1() ) )
```

Since both sub-expressions, the literals `1`, are identical, their serializations are equal as well:
```
{
  kind: "ValEx",
  type: "Int",
  value: {
    kind: "TlaInt",
    value: 1
  }
}
```

Note that in the above example, the outer `value` field contains a JSON serialization of `TlaInt(1)`, and not just the JSON literal `1`. This is because of deserialization:
Apalache encodes its TLA+ integers as `BigInt`, which means that it permits values, for which `.isValidInt` does not hold. If we chose to encode values directly as JSON numbers, we would need a) a sensible encoding of `BigInt` values, which are not valid integers and b) a way to distinguish both variants of `BigInt`, as well as decimals, when deserializing (since JSON is not typed).
Alternatively, we could encode all values as strings, which would be similarly indistinguishable when deserializing. Importantly, the `type` field is not guaranteed to contain a hint, as it could be `Untyped`.
For the above reasons, we choose to instead serialize `TlaValue` as a JSON object, which is more verbose, but trivial to deserialize. It has the following shape
```
{
  kind: _
  value: _
}
```

The `value` field depends on the kind of `TlaValue`:
1. For `TlaStr`: a JSON string
1. For `TlaBool`: a JSON Boolean
1. For `TlaInt(bigIntValue)`: 
  1. If `bigIntValue.isValidInt`: a JSON number
  2. Otherwise: `{ bigInt: bigIntValue.toString() }`
1. For `TlaDecimal(decValue)`: a JSON string `decValue.toString`

Take `jsonOf1` to be the serialization of `ValEx( TlaInt( 1 ) )( typeTag = Typed( IntT1() ) )` shown above. The serialization of `1 + 1` is then equal to
```
{
  kind: "OperEx",
  type: "Int",
  oper: "(+)",
  args: [jsonOf1, jsonOf1]
}
```
In general, for any given `oper: TlaOper` of `OperEx`, the value of the `oper` field in the serialization equals `oper.name`.

## 5. Implementation

The implementation of the serialization can be found in the class
`at.forsyte.apalache.io.json.TlaToJson` of the module `tla-import`, see [TlaToJson][].

[ADR-002]: https://apalache.informal.systems/docs/adr/002adr-types.html

[ADR-004]: https://apalache.informal.systems/docs/adr/004adr-annotations.html

[TlaToJson]: https://github.com/informalsystems/apalache/blob/unstable/tla-import/src/main/scala/at/forsyte/apalache/io/json/TlaToJson.scala
