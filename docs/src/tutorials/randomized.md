# Tutorial on Checking ERC20 with Property-Based Testing and TLA+

**Difficulty: Blue trail – Medium**

In this tutorial, we discuss the API of the [ERC20][] tokens, which are
commonly used in the [Ethereum][] blockchain. This API is particularly
interesting, as it has a well-known [EIP20 attack vector][], discussed
in [EIP20][].

We demonstrate how one can model this API in Python and test it via stateful
testing, which is popularized by property-based testing tools such as
[Hypothesis][].

Further, we show how to specify this API in TLA+ and check it with Apalache.
Our hope is that our tutorial would bring some clarity in the relative strengths
and weaknesses of the two approaches.

## 1. Prerequisites

In this tutorial, we do not explain the basics of TLA+. If you need such a
tutorial, check [Entry-level Tutorial on the Model Checker][].

We assume that you have Apalache installed. If not, check the manual page on
[Apalache installation][]. The minimal required version is 0.25.4.

Additionally, in this tutorial we assume that you understand property-based
testing. In particular, we are using the [Hypothesis][] framework for [Python][].

## 2. Running example: ERC20

As a running example, we consider a smart contract that implements an [ERC20][]
token. To understand this example, you do not have to know much about
blockchains and smart contracts. In a nutshell, ERC20 implements a protocol, in
which every user holds some amount of tokens. For simplicity, we can assume
that we have only three users: Alice, Bob, and Eve. For example, at some point
the balances of their tokens may be as follows:

```
  balanceOf["Alice"] == 3
  balanceOf["Bob"] == 5
  balanceOf["Eve"] == 10
```

If our users are only holding their tokens, it is a little bit boring. In ERC20,
they can transfer tokens via a "transfer" transaction:

```
  transfer(sender, toAddr, value)
```

By invoking a "transfer" transaction, the user `sender` transfers `value`
tokens to the user whose address is stored in `toAddr`, provided that the
sender has at least `value` tokens on their balance. Technically, contracts
store the balances for addresses, not users, but we will be talking about
users, to keep things simple.

Consider the following two transactions:

```
  transfer("Alice", "Bob", 2)   # transaction A
  transfer("Bob", "Eve", 6)     # transaction B
```

In the above example, Alice sends two tokens to Bob, and Bob sends six tokens
to Eve. Interestingly, if transaction B is processed before transaction A,
then transaction B will fail, since Bob has only 5 tokens in his account.

Things get interesting, when we consider the possibility that some of the users
are actually programs (called smart contracts). Say, Eve is a smart contract.
It often happens that the human users want that smart contracts do token
transfer  on their behalf. However, it would be a bit dangerous, if a contract
could transfer an arbitrary number of tokens from the user's account. To this
end, ERC20 has "approve" transactions:

```
  approve(sender, spender, value)
```

By invoking an "approve" transaction, the user `sender` authorizes the user
`sender` to transfer at most `value` tokens on the behalf of `sender`. However,
the spender cannot do such a transfer via a "transfer" transaction. Hence,
ERC20 introduces a third type of transactions:

```
  transferFrom(sender, fromAddr, toAddr, value)
```

By invoking a "transferFrom" transaction, the sender is transferring `value`
tokens from the address `fromAddr` on the address `toAddr`. This can only be
done, if `sender` was authorized to transfer at least `value` tokens from the
address `fromAddr`.

Although this API seems to be quite reasonable, the [EIP20 attack vector][]
shows that it may behave in a way that some users do not expect. We refer the
reader to the above document. Here we give a sequence of problematic
transactions:

![The sequence of transactions](./img/erc20.drawio.svg)

Here is what is happening in the above example. Alice approves Bob to transfer
up to 3 tokens. This transaction is added to the transaction pool, but it is
not committed immediately, as it takes the consensus engine some time to select
this transaction and commit it. Meanwhile, Alice decides to lower her approval
to Bob, and she issues another "approve" transaction that limits the amount of
tokens to 2. However, Bob is actively monitoring the transaction pool, and he
observes that there are two approvals issued by Alice. So he quickly issues a
"transferFrom" transaction. If he gets lucky (e.g., he gives more gas to his
transaction than Alice did), then his transfer happens after the first approval
but before the second approval. If that happened, he issues another
"transferFrom" transaction and collects five tokens in total, though Alice's
intention was to authorize Bob to transfer up to three tokens (and later, even
two tokens instead of three).

Can we use some automation to discover such an execution? By looking at the
above example, we can see that the core of this question is whether we can find
the following sequence of events:

  1. submit `tx1: approve(u1, u2, n)` where `n > 0` and `u1 != u2`
  1. submit `tx2: approve(u1, u2, m)` where `m > 0`
  1. submit `tx3: transferFrom(u2, u1, u3, k)` where `m < k <= n`, `u3 != u2`
     and `u3 != u1`
  1. commit `tx1`
  1. commit `tx3`

Once we have reached a state via the sequence of events 1-5, we can see that
it should be possible to extend it with the following events:

  6. commit `tx2`
  1. submit `tx4: transferFrom(u2, u1, u3, l)`
     where `0 < l <= m`, `u3 != u2` and `u3 != u1`
  1. commit `tx4`

Hence, in the rest of this tutorial, we focus on finding a valid sequence of
events 1-5.  

## 3. Stateful testing with Hypothesis

Since we are talking about an API, it is quite tempting to express this API in
a programming language, for example, in [Python][]. We give only the interesting
parts of the code. A complete example is available in [test_erc20.py][].

### 3.1. Restricting the scope

Before writing the code of the transactions, we should think about the scope of
our tests:

 - *Do we have to run the tests against the actual blockchain?*
   It does not seem that we need that to reason about the API.

 - *Do we have to use the actual Ethereum data structures?*
   Again, this is not needed for reasoning about the API.

 - *Do we have to express amounts as 256-bit integers (as in Ethereum)
    and search over the full range of Ethereum addresses (20 bytes)?*

The last question is of particular interest, as the search spaces in modern
programming languages are simply astronomic. We assume the small scope
hypothesis, which is usually put like this at [Alloy Wikipedia page][]:

    ...a high proportion of bugs can be found by testing a program for all test
    inputs within some small scope.

By following this hypothesis, we limit the space of addresses and amounts to
small sets (in Python):

```tla
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:23:28}}
```

### 3.2. Introducing transactions

Following ERC20, we introduce three classes of transactions in Python:

```tla
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:31:58}}
```

### 3.3. Introducing and initializing the state machine

We model the API of ERC20 as a [rule-based state machine]. As explained in the
documentation of the Hypothesis library, we introduce a class that
models executions of this state machine:

```tla
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:60:67}}

    # more code follows...
```

The testing framework uses this state machine to randomly generate executions
that are described by a set of rules, which we present below. Before, we dive
into the rules, we have to initialize the state machine for every run:

```tla
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:72:87}}
```

The code of the method `init` is self-explanatory. The most interesting part
belongs to the annotation inside `@initialize(...)`. Basically, it tells the
testing framework that the input parameter `amounts` should be a randomly
generated list, whose elements are randomly drawn from the list `AMOUNTS`. We
limit the size of the list `amount` with the parameters `min_size` and
`max_size`. To better understand generators, check the page on the [Hypothesis
generators][].

We have to explain Hypothesis, where to generate transactions and where to read
them from. This is done via bundles. To this end, we introduce a bundle:

```tla
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:68:70}}
```

### 3.4. Generating transactions

To generate "transfer" transactions, we introduce the rule `submit_transfer`:

```tla
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:88:96}}
```

Similar to `init`, the method parameters `_sender`, `_toAddr`, and `_value` are
randomly drawn from the lists `ADDR` and `AMOUNTS`. A generated transaction of
type `TransferTx` is added to the bundle `pendingTxs`, which is specified via
the parameter `target` in the annotation `@rule`.

We will see later that bundles cannot be used for specifying invariants.
Hence, we add the transaction to a shadow copy, which we call
`self.pendingTxsShadow`. Additionally, we reset `self.lastTx`. This will be
also needed for writing an invariant.

We define the rules `submit_transferFrom` and `submit_approve` similar to
`submit_transfer`:

```tla
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:97:115}}
```

### 3.5. Committing transactions

To commit a generated transaction, we introduce the rule `commit_transfer`:

```tla
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:116:127}}
```

The large part of the above code should be clear. However, there are two new
constructs in `commit_transfer`. First, we consume a transaction via
`tx=consumes(pendingTxs)`, which deletes a transaction from the bundle
`pendingTxs` and places it in the input parameter `tx`. On top of that, we add
the statement `assume(...)` inside the method. This statement tells the testing
framework to reject the cases that violate the assumption.

Similar to `commit_transfer`, we define the rules `commit_transfer_from` and
`commit_approve`:

```tla
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:129:152}}
```

### 3.6. Introducing state invariants

Since we are writing a test to check some properties, we have to specify these
properties. The simplest property that we want to test is whether the account
balances may go negative:

```tla
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:153:157}}
```

There is not much to explain about the above code. It is important to
understand that this invariant is checked after execution of `init` and after
execution of every rule in a test run.

We also write an invariant that we actually want to test:

```
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:159:174}}
```

The above invariant specifies the situation that we discussed in Section 2.

### 3.7. Generating the test runs

Finally, we add the test class to the test suite:

```
{{#include ../../../test/tla/tutorials/randomized/test_erc20.py:193:202}}
```

The most important parameters are as follows:

 - `max_examples` limits the number of test executions to generate,
 - `stateful_step_count` limits the length of test executions, and
 - `deadline` limits the running time of every execution,
   which we set to `None`, as the running times may vary.

We run the test with the Python testing framework as follows:   

```sh
pytest --hypothesis-show-statistics
```

We have run the test five times. Each run took 1.5 hours on average. Here is
the typical output by `pytest`:

```  
  - Typical runtimes: 0-3 ms, ~6% in data generation
   - 100000 passing examples, 0 failing examples, 365850 examples
   - Events:
    * 8.82%, approve
    * 1.73%, transfer
    * 0.00% transferFrom
```

Finally, on the sixth run, the test has detected an invariant violation after
34 minutes:

```
  Falsifying example:
  state = Erc20Simulator()
  state.init(amounts=[0, 0, 2])
  state.all_transfers_approved()
  state.non_negative_balances()
  v1 = state.submit_approve(_sender='Eve', _spender='Alice', _value=1)
  state.all_transfers_approved()
  state.non_negative_balances()
  v2 = state.submit_approve(_sender='Eve', _spender='Alice', _value=2)
  state.all_transfers_approved()
  state.non_negative_balances()
  state.commit_approve(tx=v2)
  state.all_transfers_approved()
  state.non_negative_balances()
  v3 = state.submit_transfer_from(_fromAddr='Eve',
                                  _sender='Alice', _toAddr='Bob', _value=2)
  state.all_transfers_approved()
  state.non_negative_balances()
  state.commit_transfer_from(tx=v3)
  state.all_transfers_approved()
  state.teardown()
```

Cool! We have managed to find the expected invariant violation, though it took
us about 8 hours and about 2 million runs to enumerate. 

### 3.8. Why does it take so long?

Let's do a bit of math to better understand the probability of finding a bug
with our approach. If you can propose a more precise analysis, please let us
know.

As we discussed above, we have to produce a sequence that contains 5 events.
Let's focus on the probability of randomly producing a run that contains five
rules:

 - At every step, we randomly choose one out of six rules.
   - If we choose `submit_transfer`, we have
     `len(ADDR) * len(ADDR) * len(AMOUNTS) = 3 * 3 * 20 = 180`
     combinations to choose from.
   - If we choose `submit_transferFrom`, we have
     `len(ADDR) * len(ADDR) * len(ADDR) * len(AMOUNTS) = 3 * 3 * 3 * 20 = 540`
     combinations to choose from.
   - If we choose `submit_approve`, we have
     `len(ADDR) * len(ADDR) * len(AMOUNTS) = 3 * 3 * 20 = 180`
     combinations to choose from.
   - If we choose `commit_transfer`, we restrict the combinations of
     amounts and addresses with `assume`,
     so this gives us a multiplier `(1 / 2) * (190 / (20 * 20)) = 0.2375`
   - If we choose `commit_approve`, we restrict the combinations of
     amounts and addresses with `assume`,
     so this gives us a multiplier `(1 / 2) * (19 / 20) = 0.475`
   - If we choose `commit_transfer_from`, we restrict the combinations of
     amounts and addresses with `assume`,
     so this gives us a multiplier `(1 / 2) * (190 / (20 * 20))^2 = 0.1128125`.

To count the number of valid runs that contain 5 rules, we execute a custom
script [count_combinations.py][]. This script gives us 591e12 combinations.

Although the search space is quite large, we have to understand the number of
runs that violate the invariant `all_transfers_approved`. Maybe this number is
of comparable size?

Recall that we are looking for the following sequence, which is pretty much
fixed:

  1. submit `tx1: approve(u1, u2, n)` where `n > 0` and `u1 != u2`
  1. submit `tx2: approve(u1, u2, m)` where `m > 0`
  1. submit `tx3: transferFrom(u2, u1, u3, k)` where `m < k <= n`, `u3 != u2`
     and `u3 != u1`
  1. commit `tx1`
  1. commit `tx3`

How many combinations do we have here? We see that all three addresses `u1`,
`u2`, and `u3` must distinct. Hence, the number of combinations for producing
these addresses is `3! = 6`. The choice of `n` is unrestricted, so we have
`len(AMOUNTS) = 20` combinations. As for `m` and `k`, we have the constraint
`m < k <= n`. We can easily compute the number of the combinations for `n`, `m`,
and `k` with a Python loop:

```python
  sum = 0
  for n in range(1, 20);
      for k in range(1, n + 1):
          for m in range(1, k):
              sum += 1
  print(sum)
  # 1140
```

Hence, we have `6 * 1140 = 6840` runs that violate the invariant.  This gives
is 6840 chances in 591e12. This is about 1 chance in 86 billion, assuming the
uniform distribution. We were quite lucky that Hypothesis has reported an
invariant violation after exploring about 2 million runs (after exploring runs
for 8 hours). Perhaps, Hypothesis is using clever heuristics to enumerate runs.

### 3.9. Lessons learned

Some lessons learned:

 - It took us several iterations to debug the Python code,
   since these errors are only reported at runtime. To strengthen the model,
   we would have to write unit tests for the simulator.

 - Since the tests take a lot of time, there is always a doubt about whether
   the invariants are written correctly. It is not easy to guide the framework
   into an interesting state.

 - Random exploration is producing plenty of invalid executions (about 80% in
   our case), which are rejected by the framework.

 - We had to carefully tune the maximum number of steps in a single run.
   Further increasing the number of steps would lead to further decrease in the
   probability of finding an invariant violation.

 - Given our complexity estimates and the running times, it looks like our
   example is on the edge of what is feasible with Hypothesis.

## 4. Symbolic simulation with Apalache

Let us repeat the same exercise with TLA+ and Apalache. Although TLA+ is not a
programming language, we will see that the TLA+ specification is structurally
quite similar to the test that we have developed for Hypothesis. In contrast to
8 hours of running PBT, we find the same execution with Apalache in 16 seconds.
So it is probably worth looking at.

We assume that you already know the basics of TLA+. The complete specification
and its model checking instance can be found in [ERC20.tla][] and
[MC_ERC20.tla][].

### 4.1. The shape of the state machine

Similar to our Python code in [test_erc20.py][], we declare the set of all
addresses. In contrast to the code, we declare `ADDR` to be a constant, which
is instantiated later:

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:17:22}}
```

Since we specify a state machine, we declare the state variables of our state
machine that we obviously need for [ERC20][]:

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:23:34}}
```

Similar to the Python code, we declare additional state variables:

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:35:52}}
```

### 4.2. Initializing the state machine

As usual, we describe the initial states via the predicate `Init`:

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:53:63}}
```

### 4.3. Submitting transactions

To submit a "transfer" transaction, we introduce the action `SubmitTransfer`:

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:74:82}}
```

The above code is simple. We construct a transaction as a record and add
it to the set of the pending transactions.

Similar to that, we define the actions `SubmitApprove` and `SubmitTransferFrom`:

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:162:172}}
```

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:118:129}}
```

### 4.4. Committing transactions

To commit a transfer transaction, we introduce the action `CommitTransfer`:

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:86:103}}
```

The interesting aspect here is that we mark a transaction as failed, if it
violates the validation rules. Although it is not of importance in this
tutorial, it is a good pattern, which lets us to produce transactions that can
be used to test the actual implementation with an end-to-end testing framework
such as [Atomkraft][].

Similar to `CommitTransfer`, we define the action `CommitApprove` and
`CommitTransferFrom`:


```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:133:155}}
```

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:175:187}}
```

### 4.5. Introducing the transition predicate

As usual, we introduce the predicate called `Next` that captures the choice of
actions:

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:189:204}}
```

We non-deterministically pick one of the six actions at each step. The action
parameters are non-deterministically chosen via the operator "exists", e.g.,
`\E value \in Int`. Note that we simply draw integer values from the set of all
integers, as there is no need to restrict this set. Although TLA+ as a language
does not have randomization, some tools may interpret non-determinism as random
choice.

### 4.6. Introducing state invariants

Similar to `all_transfers_approved` in [test_erc20.py][], we define the
following state invariant:

```
{{#include ../../../test/tla/tutorials/randomized/ERC20.tla:236:250}}
```

### 4.6. Introducing an instance for model checking

Our TLA+ specification is parameterized in the set `ADDR`. In order to run
Apalache, we have to initialize this constant. The complete code can be found
in [MC_ERC20.tla][]. The most important definition is as follows:

```tla
\* Use the set of three addresses.
\* We are using uninterpreted values, similar to TLC's model values.
\* See: https://apalache.informal.systems/docs/HOWTOs/uninterpretedTypes.html
ADDR == { "Alice_OF_ADDR", "Bob_OF_ADDR", "Eve_OF_ADDR" }
```

### 4.7. Checking the invariant via symbolic simulation

Having defined the specification and its instance, we run Apalache to perform
symbolic simulation:

```sh
$ apalache-mc simulate --length=10 --max-run=10000 \
  --inv=NoTransferFromWhileApproveInFlight MC_ERC20.tla
```


[ERC20]: https://ethereum.org/en/developers/docs/standards/tokens/erc-20/
[EIP20]: https://eips.ethereum.org/EIPS/eip-20
[EIP20 attack vector]: https://docs.google.com/document/d/1YLPtQxZu1UAvO9cZ1O2RPXBbT0mooh4DYKjA_jp-RLM/edit#
[Ethereum]: https://ethereum.org/en/
[Hypothesis]: https://hypothesis.readthedocs.io/
[Python]: https://www.python.org/
[Apalache installation]: ../apalache/installation/index.md
[Entry-level Tutorial on the Model Checker]: ./entry-tutorial.md
[test_erc20.py]: https://github.com/informalsystems/tla-apalache-workshop/blob/main/examples/erc20-approve-attack/test_erc20.py
[Alloy Wikipedia page]: https://en.wikipedia.org/wiki/Alloy_(specification_language)
[rule-based state machine]: https://hypothesis.readthedocs.io/en/latest/stateful.html#rule-based-state-machines
[Hypothesis generators]: https://hypothesis.readthedocs.io/en/latest/data.html
[count_combinations.py]: https://github.com/informalsystems/tla-apalache-workshop/blob/main/examples/erc20-approve-attack/count_combinations.py
[ERC20.tla]: https://github.com/informalsystems/tla-apalache-workshop/blob/main/examples/erc20-approve-attack/ERC20.tla
[MC_ERC20.tla]: https://github.com/informalsystems/tla-apalache-workshop/blob/main/examples/erc20-approve-attack/MC_ERC20.tla
[Atomkraft]: https://github.com/informalsystems/atomkraft
