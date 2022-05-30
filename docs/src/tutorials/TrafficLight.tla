---- MODULE TrafficLight ----
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

\* @type: <<Bool, Bool>>;
vars == << isGreen, requestedGreen >>

\* The light is initially red, and the button was not pressed.
Init ==
    /\ isGreen = FALSE
    /\ requestedGreen = FALSE

(* ---------------------- *)
(* requesting green light *)
\* The switch to green can only be requested when the light is not green, and
\* the switch has not *already* been requested since the light last turned green.
CanRequestGreen ==
    /\ ~isGreen
    /\ ~requestedGreen

RequestGreen == 
    /\ requestedGreen' = TRUE
    /\ UNCHANGED << isGreen >>

(* ---------------------- *)
(* switching to red light *)
\* The light can switch to red at any time if it is currently green.
CanSwitchToRed == isGreen

SwitchToRed ==
    /\ isGreen' = FALSE
    /\ UNCHANGED << requestedGreen >>

(* ------------------------ *)
(* switching to green light *)
\* The light can switch to green if it is currently red, and
\* the button to request the switch to green has been pressed.
CanSwitchToGreen == 
    /\ ~isGreen
    /\ requestedGreen

SwitchToGreen ==
    /\ isGreen' = TRUE
    /\ requestedGreen' = FALSE

Next ==
    \/ CanRequestGreen /\ RequestGreen
    \/ CanSwitchToRed /\ SwitchToRed
    \/ CanSwitchToGreen /\ SwitchToGreen

RequestWillBeFulfilled ==
    [](requestedGreen => <>isGreen)

StutteringNext ==
    [Next]_vars

====