----------------------------- MODULE MC_ERC20 ---------------------------------
\* an instance for model checking ERC20.tla with Apalache
EXTENDS ERC20_typedefs

\* Use the set of three addresses.
\* We are using uninterpreted values, similar to TLC's model values.
\* See: https://apalache.informal.systems/docs/HOWTOs/uninterpretedTypes.html
ADDR == { "Alice_OF_ADDR", "Bob_OF_ADDR", "Eve_OF_ADDR" }

VARIABLES
    \* @type: ADDR -> Int;
    balanceOf,
    \* @type: <<ADDR, ADDR>> -> Int;
    allowance,
    \* @type: Set(TX);
    pendingTransactions,
    \* Last executed transaction.
    \* @type: TX;
    lastTx,
    \* @type: Int;
    nextTxId

\* instantiate the spec with ADDR, balances, allowances, and pendingTxs
INSTANCE ERC20

===============================================================================
