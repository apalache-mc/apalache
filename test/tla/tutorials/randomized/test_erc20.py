#!/usr/bin/env python3
#
# Modeling ERC20 tokens of Ethereum and the Approve-TransferFrom Attack:
#
# EIP-20: https://eips.ethereum.org/EIPS/eip-20
#
# Attack scenario:
#   https://docs.google.com/document/d/1YLPtQxZu1UAvO9cZ1O2RPXBbT0mooh4DYKjA_jp-RLM/edit#
#
# Our testing framework is designed towards checking the protocol features.
# We do not model 256-bit integers here, as we are not interested in overflows.
# 
# Igor Konnov, Informal Systems, 2021-2022


import unittest

from hypothesis import given, strategies as gen
from hypothesis.stateful import Bundle, RuleBasedStateMachine
from hypothesis.stateful import rule, consumes, invariant, initialize
from hypothesis import assume, settings, event, Verbosity

# The list of addresses to use. We could use real addresses here,
# but simple readable names are much nicer.
ADDR = [ "Alice", "Bob", "Eve" ]

# We restrict the amounts to a small range, to avoid too much randomness
AMOUNTS = range(0, 20)


class TransferTx:
    """An instance of transfer"""

    def __init__(self, sender, toAddr, value):
        self.tag = "transfer"
        self.sender = sender
        self.toAddr = toAddr
        self.value = value

class TransferFromTx:
    """An instance of transferFrom"""

    def __init__(self, sender, fromAddr, toAddr, value):
        self.tag = "transferFrom"
        self.sender = sender
        self.fromAddr = fromAddr
        self.toAddr = toAddr
        self.value = value

class ApproveTx:
    """An instance of approve"""

    def __init__(self, sender, spender, value):
        self.tag = "approve"
        self.sender = sender
        self.spender = spender
        self.value = value


class Erc20Simulator(RuleBasedStateMachine):
    """
    Model the behavior of the ERC20 API in terms of stateful testing.
    """

    def __init__(self):
        super().__init__()

    # This bundle contains the generated transactions
    # that are to be processed
    pendingTxs = Bundle("pendingTxs")

    @initialize(amounts=gen.lists(gen.sampled_from(AMOUNTS),
                min_size=len(ADDR),
                max_size=len(ADDR)))
    def init(self, amounts):
        # balance of every account
        self.balanceOf = {
            addr: amount for (addr, amount) in zip(ADDR, amounts)
        }
        # approvals from senders to spenders
        self.allowance = {
            (sender, spender): 0 for sender in ADDR for spender in ADDR
        }
        # history variables that we need to express the invariants
        self.pendingTxsShadow = set()
        self.lastTx = None

    @rule(target=pendingTxs, _sender=gen.sampled_from(ADDR),
          _toAddr=gen.sampled_from(ADDR), _value=gen.sampled_from(AMOUNTS))
    def submit_transfer(self, _sender, _toAddr, _value):
        # submit a transfer transaction on the client side
        tx = TransferTx(_sender, _toAddr, _value)
        self.pendingTxsShadow.add(tx)
        self.lastTx = None
        return tx

    @rule(target=pendingTxs, _sender=gen.sampled_from(ADDR),
          _fromAddr=gen.sampled_from(ADDR),
          _toAddr=gen.sampled_from(ADDR), _value=gen.sampled_from(AMOUNTS))
    def submit_transfer_from(self, _sender, _fromAddr, _toAddr, _value):
        # submit a transferFrom transaction on the client side
        tx = TransferFromTx(_sender, _fromAddr, _toAddr, _value)
        self.pendingTxsShadow.add(tx)
        self.lastTx = None
        return tx

    @rule(target=pendingTxs, _sender=gen.sampled_from(ADDR),
          _spender=gen.sampled_from(ADDR), _value=gen.sampled_from(AMOUNTS))
    def submit_approve(self, _sender, _spender, _value):
        # submit an approve transaction on the client side
        tx = ApproveTx(_sender, _spender, _value)
        self.pendingTxsShadow.add(tx)
        self.lastTx = None
        return tx

    @rule(tx=consumes(pendingTxs))
    def commit_transfer(self, tx):
        # process a transfer transaction somewhere in the blockchain
        assume(tx.tag == "transfer"
               and tx.value <= self.balanceOf[tx.sender]
               and tx.value > 0
               and tx.sender != tx.toAddr)
        self.pendingTxsShadow.remove(tx)
        self.balanceOf[tx.sender] -= tx.value
        self.balanceOf[tx.toAddr] += tx.value
        self.lastTx = tx
        event("transfer")

    @rule(tx=consumes(pendingTxs))
    def commit_transfer_from(self, tx):
        # process a transferFrom transaction somewhere in the blockchain
        assume(tx.tag == "transferFrom"
               and tx.value > 0
               and tx.value <= self.balanceOf[tx.fromAddr]
               and tx.value <= self.allowance[(tx.fromAddr, tx.sender)]
               and tx.fromAddr != tx.toAddr)
        self.pendingTxsShadow.remove(tx)
        self.balanceOf[tx.fromAddr] -= tx.value
        self.balanceOf[tx.toAddr] += tx.value
        self.allowance[(tx.fromAddr, tx.sender)] -= tx.value
        self.lastTx = tx
        event("transferFrom")

    @rule(tx=consumes(pendingTxs))
    def commit_approve(self, tx):
        # process an approve transaction somewhere in the blockchain
        assume(tx.tag == "approve" and tx.value > 0 and tx.sender != tx.spender)
        self.pendingTxsShadow.remove(tx)
        self.allowance[(tx.sender, tx.spender)] = tx.value
        self.lastTx = tx
        event("approve")

    @invariant()
    def non_negative_balances(self):
        # a simple invariant to make sure that the balances do not go negative
        for addr in ADDR:
            assert(self.balanceOf[addr] >= 0)

    @invariant()
    def all_transfers_approved(self):
        # If this invariant is violated, then it is possible to transfer tokens
        # (based on an earlier approval), while there is an approval for a
        # smaller amount in the pending transactions
        last = self.lastTx
        if last:
            if last.tag == "transferFrom" and last.value > 0:
                for p in self.pendingTxsShadow:
                    if p.tag == "approve" \
                            and p.sender == last.fromAddr \
                            and p.spender == last.sender \
                            and last.sender != last.toAddr \
                            and p.value < last.value and p.value > 0:
                        assert(False)

    # Uncomment the following invariant to check,
    # whether it is possible to have allowances in progress.
#    @invariant()
#    def no_approval(self):
#        for sender in ADDR:
#            for spender in ADDR:
#                assert(self.allowance[(sender, spender)] <= 0)

    # Uncomment the following invariant to check,
    # whether it is possible to have allowances in progress.
#    @invariant()
#    def no_transfers_from(self):
#        for sender in ADDR:
#            for spender in ADDR:
#                total = self.histSumTransferFrom[(sender, spender)]
#                assert(total == 0)


# run stateful testing
TestTrees = Erc20Simulator.TestCase
Erc20Simulator.TestCase.settings = settings(
    max_examples=100000,
    stateful_step_count=7,
    deadline=None
)

if __name__ == "__main__":
    unittest.main()
