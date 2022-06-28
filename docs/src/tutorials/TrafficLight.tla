---- MODULE TrafficLight ----
\* ANCHOR: vars
VARIABLES 
    \* If true, the traffic light is green. If false, it is red.
    \* @type: Bool;
    isGreen,

    \* If true, the button has been pushed to request the light to become green, but the light has
    \* not become green since then.
    \* If false, the light has become green since the button has last been pushed
    \* or the button has never been pushed.
    \* @type: Bool;
    requestedGreen
\* ANCHOR_END: vars

\* ANCHOR: init
\* The light is initially red, and the button was not pressed.
Init ==
    /\ isGreen = FALSE
    /\ requestedGreen = FALSE
\* ANCHOR_END: init

\* ANCHOR: actions
(* ---------------------- *)
(* requesting green light *)
\* The switch to green can only be requested when the light is not green, and
\* the switch has not *already* been requested since the light last turned green.
RequestGreen_Guard ==
    /\ ~isGreen
    /\ ~requestedGreen

RequestGreen_Effect == 
    /\ requestedGreen' = TRUE
    /\ UNCHANGED << isGreen >>

RequestGreen ==
    RequestGreen_Guard /\ RequestGreen_Effect

(* ---------------------- *)
(* switching to red light *)
\* The light can switch to red at any time if it is currently green.
SwitchToRed_Guard == isGreen

SwitchToRed_Effect ==
    /\ isGreen' = FALSE
    /\ UNCHANGED << requestedGreen >>

SwitchToRed ==
    SwitchToRed_Guard /\ SwitchToRed_Effect

(* ------------------------ *)
(* switching to green light *)
\* The light can switch to green if it is currently red, and
\* the button to request the switch to green has been pressed.
SwitchToGreen_Guard == 
    /\ ~isGreen
    /\ requestedGreen

SwitchToGreen_Effect ==
    /\ isGreen' = TRUE
    /\ requestedGreen' = FALSE

SwitchToGreen ==
    SwitchToGreen_Guard /\ SwitchToGreen_Effect

Next ==
    \/ RequestGreen
    \/ SwitchToRed
    \/ SwitchToGreen
\* ANCHOR_END: actions

\* ANCHOR: prop
RequestWillBeFulfilled ==
    [](requestedGreen => <>isGreen)
\* ANCHOR_END: prop

\* ANCHOR: stutternext
\* @type: <<Bool, Bool>>;
vars == << isGreen, requestedGreen >>

StutteringNext ==
    [Next]_vars
\* ANCHOR_END: stutternext

====