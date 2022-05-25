------------------------ MODULE ERC20_typedefs --------------------------------
(*
  Type definitions for the module ERC20.

  An account address, in our case, simply an uninterpreted type ADDR.

  A transaction (a la discriminated union but all fields are packed together):
  @typeAlias: TX = [
    tag: Str,
    id: Int,
    fail: Bool,
    sender: ADDR,
    spender: ADDR,
    fromAddr: ADDR,
    toAddr: ADDR,
    value: Int
  ];

  A state of the state machine:
  @typeAlias: STATE = [
    balanceOf: ADDR -> Int,
    allowance: <<ADDR, ADDR>> -> Int, 
    pendingTransactions: Set(TX),
    lastTx: TX,
    nextTxId: Int
  ];

  Below is a dummy definition to introduce the above type aliases.
 *) 
ERC20_typedefs == TRUE
===============================================================================
