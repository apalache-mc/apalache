# Idiom 0: Keep state variables to the minimum

## Description

_A good TLA+ specification minimizes the computation state and makes it visible_.

TLA+ does not have special syntax for assignments to the variables.  For a good
reason. The power of TLA+ is in writing constraints on variables rather than in
writing detailed commands. If you have been writing in languages such as C, C++,
Java, Python, your first reflex would be to define a variable to store the
intermediate result of a complex computation.

In programming languages, we introduce temporary variables for several reasons:

  1. To avoid repetitive computations of the same expression,
  1. To break down a large expression into a series of smaller expressions, 
  1. To make the code concise.

Point 1 is a non-issue in TLA+, as it is mostly executed in the reader's brain,
and people are probably less efficient in caching expressions than computers.
Points 2 and 3 can be nicely addressed with LET-definitions in TLA+. Hence,
there is no need for auxiliary variables.

Usually, we should minimize the specification state, that is, the scope of the data
structures that are declared with `VARIABLES`. It does not mean that one variable
is always better than two. It means that what is stored in `VARIABLES` should be
absolutely necessary to describe the computations or the observed properties.

## Advantages

By avoiding auxiliary state variables, we localize the updates to the state.
This improves specification readability. It also helps the tools, as large parts
of the specification become deterministic.

## Disadvantages

Sometimes, we have to expose the internals of the computation. For instance,
if we want to closely monitor the values of the computed expressions, when using
the specification for model-based testing.

## Example

Consider the following implementation of [Bubble sort] in Python:

```python
    my_list = [5, 4, 3, 8, 1]
    changed = True
    my_list_len = len(my_list)  # cache the length
    while changed:
        changed = False
        if my_list_len > 0:
            prev = my_list[0]       # save the first element to use in the loop
        for i in range(1, my_list_len):
            current = my_list[i]
            if prev <= current:
                # save current for the next iteration
                prev = current
            else:
                # swap the elements
                my_list[i - 1] = current
                my_list[i] = prev
                changed = True
```

Notice that we have introduced three local variables to optimize the code:

  - `my_list_len` to cache the length of the list,
  - `prev` to cache the previously accessed element of the list,
    in order to minimize the number of list accesses,
  - `current` to cache the iterated element of the list.

In TLA+, one usually does not introduce local variables for the intermediate
results of the computation, but rather introduces variables to represent the
essential part of the algorithm state. (While we have spent some time on code
optimization, we might have missed the fact that our sorting algorithm is not
as good as [Quicksort].) In the above example, the essential variables are
`finished` and `my_list`.

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

Our TLA+ code contains only two state variables: `my_list` and `finished`.
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
            current == my_list[i]
        IN
        /\ prev > current
        /\ my_list' = [my_list EXCEPT ![i - 1] = current, ![i] = prev]
```

However, the let-definitions are not variables, they are just aliases for more
complex expressions. Importantly, one cannot update the value of an expression
that is defined with a let-definition. In this sense, TLA+ is similar to
the functional languages, where side effects are carefully avoided and minimized.

In contrast to the functional languages, the value of TLA+ is not in computing
the result of a function application, but in producing sequences of states
(called behaviors). Hence, some parts of a TLA+ specification should have side effects:
To record the states.


[Bubble sort]: https://en.wikipedia.org/wiki/Bubble_sort
[Quicksort]: https://en.wikipedia.org/wiki/Quicksort
