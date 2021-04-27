---------------------- MODULE TestAnnotations ---------------------------------
\* test several tricky annotations

VARIABLES
    \* See issue #718
    \*
    \* @typeAlias: ELEM =
    \*             Int;
    \* @type:
    \*   Set(
    \*        ELEM
    \*      );
    \*
    \* See issue #757
    \* packetCommitments' = [packetCommitments EXCEPT
    \*    ![upcomingEvent.chain] = @ \ {upcomingEvent.packet}]
    S

Init ==
    S = {}

Next ==
    S' = {1}

Inv ==
    2 \notin S
    
\* Unit tests as proposed in RFC006
\*
\* We can use identifiers, see issue #768
\*
\* @require(Init)
\* @ensure(Assertion)
\* @testAction(5)
Test ==
    Next

===============================================================================
