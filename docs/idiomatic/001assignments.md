# Idiom 1: Let there be (few) assignments

## Description

TLA+ does not have special syntax for assignments to the variables.  For a good
reason. The power of TLA+ is in writing constraints on variables rather than in
writing detailed commands. If you have been writing in languages such as C, C++,
Java, Python, your first reflex would be to define a variable to store the
intermediate result of a complex computation.

Consider the following implementation of
[bubble sort](https://en.wikipedia.org/wiki/Bubble_sort) in Python:

```python
  in_list = [5, 4, 3, 8, 1]
  my_list = in_list
  finished = False
  while not finished:
    finished = True
    for i in range(1, len(my_list)):
      if my_list[i - 1] > my_list[]:
        tmp = my_list[i - 1]
        my_list[i - 1] = my_list[i]
        my_list[i] = tmp
        finished = False
```

Notice that there are four assignments under the `if`-expression, one of them
introduces a local variable `tmp`. In TLA+, one does not
introduce local variables for the intermediate results of the computation, but rather
introduces variables to represent the essential part of the algorithm state. In the
above example, the essential variables are `finished` and `my_list`.

Compare the above code to (a slightly more abstract) [bubble sort in
TLA+](./example/bubble.tla):

```tla
EXTENDS Integers, Sequences

in_list == <<5, 4, 3, 8, 1>>
VARIABLES my_list, finished

Init ==
    /\ my_list = in_list
    /\ finished = FALSE

IsSorted(lst) ==
    \A i \in DOMAIN lst \ {1}:
        lst[i - 1] <= lst[i]

WhenSorted ==
    /\ IsSorted(my_list)
    /\ finished' = TRUE
    /\ UNCHANGED my_list

WhenUnsorted ==
    /\ \E i \in DOMAIN my_list \ {1}:
        /\ my_list[i - 1] > my_list[i]
        /\ my_list' = [my_list EXCEPT ![i - 1] = my_list[i],
                                      ![i] = my_list[i - 1]]
    /\ finished' = FALSE

Next ==
    IF finished
    THEN UNCHANGED <<my_list, finished>>
    ELSE WhenSorted \/ WhenUnsorted

```

The TLA+ code contains only two state variables: `my_list` and `finished`.
Other variables are introduced by quantifiers (e.g., `\E i \in ...`).
The state variables are not updated in the sense of programming languages.
Rather, one writes constraints over unprimed and primed versions, e.g.:

```tla
        ...
        /\ my_list' = [my_list EXCEPT ![i - 1] = my_list[i],
                                      ![i] = my_list[i - 1]]
```

Of course, one can introduce aliases for intermediate expressions, for instance,
by using let-definitions:

```tla
        ...
        LET prev == my_list[i - 1]
            next == my_list[i]
        IN
        /\ prev > next
        /\ my_list' = [my_list EXCEPT ![i - 1] = next, ![i] = prev]
```

However, the let-definitions are not variables, they are just aliases of more
complex expressions. Importantly, one cannot update the value of an expression
that is defined with a let-definition. In this sense, TLA+ is similar to
the functional languages, where side effects are carefully avoided and minimized.

In contrast to the functional languages, the value of TLA+ is not in computing
the result of a function application, but in producing sequences of states
(called behaviors). 

## Example

## Advantages

## Disadvantages

