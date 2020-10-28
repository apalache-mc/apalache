#/usr/bin/env bash

# how long the execution is supposed to be
K="$1"

OUT="TwoPhaseUFO$K.smt"

cat >$OUT <<EOF
; A hand-written encoding of TwoPhaseUFO.
; Inspired by IVy (but I don't know how close it is to IVy).
;
; Igor Konnov, June 2020

; the sort of resource managers
(declare-sort RM)
;(declare-fun rm1 () RM)
;(declare-fun rm2 () RM)
;(declare-fun rm3 () RM)
; the sort of TM states, we could use an ADT, but we don't
(declare-sort TMState)
(declare-fun TMinit () TMState)
(declare-fun TMaborted () TMState)
(declare-fun TMcommitted () TMState)

(assert (distinct TMinit TMaborted TMcommitted))

; the sort of actions
(declare-sort Action)
(declare-fun TMCommit () Action)
(declare-fun TMAbort () Action)
(declare-fun TMRcvPrepared () Action)
(declare-fun RMPrepare () Action)
(declare-fun RMChooseToAbort () Action)
(declare-fun RMRcvCommitMsg () Action)
(declare-fun RMRcvAbortMsg () Action)
(assert (distinct TMCommit TMAbort TMRcvPrepared RMPrepare
    RMChooseToAbort RMRcvCommitMsg RMRcvAbortMsg))
(assert (forall ((a Action))
    (or
        (= a TMCommit)
        (= a TMAbort)
        (= a TMRcvPrepared)
        (= a RMPrepare)
        (= a RMChooseToAbort)
        (= a RMRcvCommitMsg)
        (= a RMRcvAbortMsg)
))) ;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 0
(declare-fun rmWorking_0 (RM) Bool)
(declare-fun rmPrepared_0 (RM) Bool)
(declare-fun rmCommitted_0 (RM) Bool)
(declare-fun rmAborted_0 (RM) Bool)
(declare-fun sentPrepared_0 (RM) Bool)
(declare-fun tmState_0 () TMState)

(assert (forall ((rm RM)) (rmWorking_0 rm)))
(assert (forall ((rm RM)) (not (rmPrepared_0 rm))))
(assert (forall ((rm RM)) (not (rmCommitted_0 rm))))
(assert (forall ((rm RM)) (not (rmAborted_0 rm))))
(assert (forall ((rm RM)) (not (sentPrepared_0 rm))))
(assert (= tmState_0 TMinit))
EOF

# produce a sequence of frames
for n in `seq 1 $K`; do
    p=$((n-1))
    cat >>$OUT <<EOF
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame $n
(declare-fun rmWorking_$n (RM) Bool)
(declare-fun rmPrepared_$n (RM) Bool)
(declare-fun rmCommitted_$n (RM) Bool)
(declare-fun rmAborted_$n (RM) Bool)
(declare-fun sentPrepared_$n (RM) Bool)
(declare-fun tmState_$n () TMState)

(declare-fun action_$n () Action)

; actions for frame $n
(assert (=> (= action_$n TMRcvPrepared) (and
    (= tmState_$p TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_$n rmWorking_$p)
    (forall ((rm RM)) (= (rmWorking_$n rm) (rmWorking_$p rm)))
    (forall ((rm RM)) (= (rmPrepared_$n rm) (rmPrepared_$p rm)))
    (forall ((rm RM)) (= (rmCommitted_$n rm) (rmCommitted_$p rm)))
    (forall ((rm RM)) (= (rmAborted_$n rm) (rmAborted_$p rm)))
    (forall ((rm RM)) (= (sentPrepared_$n rm) (sentPrepared_$p rm)))
    (= tmState_$n tmState_$p)
))) ;;;

(assert (=> (= action_$n TMCommit) (and
    (= tmState_$p TMinit)
    (forall ((rm RM)) (sentPrepared_$p rm))
    (= tmState_$n TMcommitted)
    (forall ((rm RM)) (= (rmWorking_$n rm) (rmWorking_$p rm)))
    (forall ((rm RM)) (= (rmPrepared_$n rm) (rmPrepared_$p rm)))
    (forall ((rm RM)) (= (rmCommitted_$n rm) (rmCommitted_$p rm)))
    (forall ((rm RM)) (= (rmAborted_$n rm) (rmAborted_$p rm)))
    (forall ((rm RM)) (= (sentPrepared_$n rm) (sentPrepared_$p rm)))
))) ;;;

(assert (=> (= action_$n TMAbort) (and
    (= tmState_$p TMinit)
    (= tmState_$n TMaborted)
    (forall ((rm RM)) (= (rmWorking_$n rm) (rmWorking_$p rm)))
    (forall ((rm RM)) (= (rmPrepared_$n rm) (rmPrepared_$p rm)))
    (forall ((rm RM)) (= (rmCommitted_$n rm) (rmCommitted_$p rm)))
    (forall ((rm RM)) (= (rmAborted_$n rm) (rmAborted_$p rm)))
    (forall ((rm RM)) (= (sentPrepared_$n rm) (sentPrepared_$p rm)))
))) ;;;

(assert (=> (= action_$n RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_$p rm)
        (not (rmWorking_$n rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_$n rm2) (rmWorking_$p rm2)))
            ) ;;;
        (rmPrepared_$n rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_$n rm2) (rmPrepared_$p rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_$n rm2) (sentPrepared_$p rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_$n rm2) (rmCommitted_$p rm2)))
        (forall ((rm2 RM)) (= (rmAborted_$n rm2) (rmAborted_$p rm2)))
        (= tmState_$n tmState_$p)
)))) ;;;

(assert (=> (= action_$n RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_$p rm)
        (not (rmWorking_$n rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_$n rm2) (rmWorking_$p rm2)))
            ) ;;;
        (rmAborted_$n rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_$n rm2) (rmAborted_$p rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_$n rm2) (rmCommitted_$p rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_$n rm2) (sentPrepared_$p rm2)))
        (= tmState_$n tmState_$p)
)))) ;;;

(assert (=> (= action_$n RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_$p TMcommitted)
        (not (rmWorking_$n rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_$n rm2) (rmWorking_$p rm2)))
            ) ;;;
        (not (rmPrepared_$n rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_$n rm2) (rmPrepared_$p rm2)))
            ) ;;;
        (rmCommitted_$n rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_$n rm2) (rmCommitted_$p rm2)))
            ) ;;;
        (not (rmAborted_$n rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_$n rm2) (rmAborted_$p rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_$n rm2) (sentPrepared_$p rm2)))
        (= tmState_$n tmState_$p)
)))) ;;;

(assert (=> (= action_$n RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_$p TMaborted)
        (not (rmWorking_$n rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_$n rm2) (rmWorking_$p rm2)))
            ) ;;;
        (not (rmPrepared_$n rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_$n rm2) (rmPrepared_$p rm2)))
            ) ;;;
        (not (rmCommitted_$n rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_$n rm2) (rmCommitted_$p rm2)))
            ) ;;;
        (rmAborted_$n rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_$n rm2) (rmAborted_$p rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_$n rm2) (sentPrepared_$p rm2)))
        (= tmState_$n tmState_$p)
)))) ;;;
EOF
done

cat >>$OUT <<EOF
;; SAFETY
(assert (or
EOF

for n in `seq 0 $K`; do
    cat >>$OUT <<EOF
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_$n rm1) (rmCommitted_$n rm2 )))
EOF
done

cat >>$OUT <<EOF
)) ;;;


(check-sat)
;;(get-model)
EOF
