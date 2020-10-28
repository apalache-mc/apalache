; A hand-written encoding of TwoPhaseUFO.
; Inspired by IVy (but I don't know how close it is to IVy).
;
; Igor Konnov, June 2020

; the sort of resource managers
(declare-sort RM)
(declare-fun rm1 () RM)
(declare-fun rm2 () RM)
(declare-fun rm3 () RM)
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 1
(declare-fun rmWorking_1 (RM) Bool)
(declare-fun rmPrepared_1 (RM) Bool)
(declare-fun rmCommitted_1 (RM) Bool)
(declare-fun rmAborted_1 (RM) Bool)
(declare-fun sentPrepared_1 (RM) Bool)
(declare-fun tmState_1 () TMState)

(declare-fun action_1 () Action)

; actions for frame 1
(assert (=> (= action_1 TMRcvPrepared) (and
    (= tmState_0 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_1 rmWorking_0)
    (forall ((rm RM)) (= (rmWorking_1 rm) (rmWorking_0 rm)))
    (forall ((rm RM)) (= (rmPrepared_1 rm) (rmPrepared_0 rm)))
    (forall ((rm RM)) (= (rmCommitted_1 rm) (rmCommitted_0 rm)))
    (forall ((rm RM)) (= (rmAborted_1 rm) (rmAborted_0 rm)))
    (forall ((rm RM)) (= (sentPrepared_1 rm) (sentPrepared_0 rm)))
    (= tmState_1 tmState_0)
))) ;;;

(assert (=> (= action_1 TMCommit) (and
    (= tmState_0 TMinit)
    (forall ((rm RM)) (sentPrepared_0 rm))
    (= tmState_1 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_1 rm) (rmWorking_0 rm)))
    (forall ((rm RM)) (= (rmPrepared_1 rm) (rmPrepared_0 rm)))
    (forall ((rm RM)) (= (rmCommitted_1 rm) (rmCommitted_0 rm)))
    (forall ((rm RM)) (= (rmAborted_1 rm) (rmAborted_0 rm)))
    (forall ((rm RM)) (= (sentPrepared_1 rm) (sentPrepared_0 rm)))
))) ;;;

(assert (=> (= action_1 TMAbort) (and
    (= tmState_0 TMinit)
    (= tmState_1 TMaborted)
    (forall ((rm RM)) (= (rmWorking_1 rm) (rmWorking_0 rm)))
    (forall ((rm RM)) (= (rmPrepared_1 rm) (rmPrepared_0 rm)))
    (forall ((rm RM)) (= (rmCommitted_1 rm) (rmCommitted_0 rm)))
    (forall ((rm RM)) (= (rmAborted_1 rm) (rmAborted_0 rm)))
    (forall ((rm RM)) (= (sentPrepared_1 rm) (sentPrepared_0 rm)))
))) ;;;

(assert (=> (= action_1 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_0 rm)
        (not (rmWorking_1 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_1 rm2) (rmWorking_0 rm2)))
            ) ;;;
        (rmPrepared_1 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_1 rm2) (rmPrepared_0 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_1 rm2) (sentPrepared_0 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_1 rm2) (rmCommitted_0 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_1 rm2) (rmAborted_0 rm2)))
        (= tmState_1 tmState_0)
)))) ;;;

(assert (=> (= action_1 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_0 rm)
        (not (rmWorking_1 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_1 rm2) (rmWorking_0 rm2)))
            ) ;;;
        (rmAborted_1 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_1 rm2) (rmAborted_0 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_1 rm2) (rmCommitted_0 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_1 rm2) (sentPrepared_0 rm2)))
        (= tmState_1 tmState_0)
)))) ;;;

(assert (=> (= action_1 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_0 TMcommitted)
        (not (rmWorking_1 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_1 rm2) (rmWorking_0 rm2)))
            ) ;;;
        (not (rmPrepared_1 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_1 rm2) (rmPrepared_0 rm2)))
            ) ;;;
        (rmCommitted_1 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_1 rm2) (rmCommitted_0 rm2)))
            ) ;;;
        (not (rmAborted_1 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_1 rm2) (rmAborted_0 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_1 rm2) (sentPrepared_0 rm2)))
        (= tmState_1 tmState_0)
)))) ;;;

(assert (=> (= action_1 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_0 TMaborted)
        (not (rmWorking_1 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_1 rm2) (rmWorking_0 rm2)))
            ) ;;;
        (not (rmPrepared_1 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_1 rm2) (rmPrepared_0 rm2)))
            ) ;;;
        (not (rmCommitted_1 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_1 rm2) (rmCommitted_0 rm2)))
            ) ;;;
        (rmAborted_1 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_1 rm2) (rmAborted_0 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_1 rm2) (sentPrepared_0 rm2)))
        (= tmState_1 tmState_0)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 2
(declare-fun rmWorking_2 (RM) Bool)
(declare-fun rmPrepared_2 (RM) Bool)
(declare-fun rmCommitted_2 (RM) Bool)
(declare-fun rmAborted_2 (RM) Bool)
(declare-fun sentPrepared_2 (RM) Bool)
(declare-fun tmState_2 () TMState)

(declare-fun action_2 () Action)

; actions for frame 2
(assert (=> (= action_2 TMRcvPrepared) (and
    (= tmState_1 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_2 rmWorking_1)
    (forall ((rm RM)) (= (rmWorking_2 rm) (rmWorking_1 rm)))
    (forall ((rm RM)) (= (rmPrepared_2 rm) (rmPrepared_1 rm)))
    (forall ((rm RM)) (= (rmCommitted_2 rm) (rmCommitted_1 rm)))
    (forall ((rm RM)) (= (rmAborted_2 rm) (rmAborted_1 rm)))
    (forall ((rm RM)) (= (sentPrepared_2 rm) (sentPrepared_1 rm)))
    (= tmState_2 tmState_1)
))) ;;;

(assert (=> (= action_2 TMCommit) (and
    (= tmState_1 TMinit)
    (forall ((rm RM)) (sentPrepared_1 rm))
    (= tmState_2 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_2 rm) (rmWorking_1 rm)))
    (forall ((rm RM)) (= (rmPrepared_2 rm) (rmPrepared_1 rm)))
    (forall ((rm RM)) (= (rmCommitted_2 rm) (rmCommitted_1 rm)))
    (forall ((rm RM)) (= (rmAborted_2 rm) (rmAborted_1 rm)))
    (forall ((rm RM)) (= (sentPrepared_2 rm) (sentPrepared_1 rm)))
))) ;;;

(assert (=> (= action_2 TMAbort) (and
    (= tmState_1 TMinit)
    (= tmState_2 TMaborted)
    (forall ((rm RM)) (= (rmWorking_2 rm) (rmWorking_1 rm)))
    (forall ((rm RM)) (= (rmPrepared_2 rm) (rmPrepared_1 rm)))
    (forall ((rm RM)) (= (rmCommitted_2 rm) (rmCommitted_1 rm)))
    (forall ((rm RM)) (= (rmAborted_2 rm) (rmAborted_1 rm)))
    (forall ((rm RM)) (= (sentPrepared_2 rm) (sentPrepared_1 rm)))
))) ;;;

(assert (=> (= action_2 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_1 rm)
        (not (rmWorking_2 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_2 rm2) (rmWorking_1 rm2)))
            ) ;;;
        (rmPrepared_2 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_2 rm2) (rmPrepared_1 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_2 rm2) (sentPrepared_1 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_2 rm2) (rmCommitted_1 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_2 rm2) (rmAborted_1 rm2)))
        (= tmState_2 tmState_1)
)))) ;;;

(assert (=> (= action_2 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_1 rm)
        (not (rmWorking_2 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_2 rm2) (rmWorking_1 rm2)))
            ) ;;;
        (rmAborted_2 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_2 rm2) (rmAborted_1 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_2 rm2) (rmCommitted_1 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_2 rm2) (sentPrepared_1 rm2)))
        (= tmState_2 tmState_1)
)))) ;;;

(assert (=> (= action_2 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_1 TMcommitted)
        (not (rmWorking_2 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_2 rm2) (rmWorking_1 rm2)))
            ) ;;;
        (not (rmPrepared_2 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_2 rm2) (rmPrepared_1 rm2)))
            ) ;;;
        (rmCommitted_2 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_2 rm2) (rmCommitted_1 rm2)))
            ) ;;;
        (not (rmAborted_2 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_2 rm2) (rmAborted_1 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_2 rm2) (sentPrepared_1 rm2)))
        (= tmState_2 tmState_1)
)))) ;;;

(assert (=> (= action_2 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_1 TMaborted)
        (not (rmWorking_2 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_2 rm2) (rmWorking_1 rm2)))
            ) ;;;
        (not (rmPrepared_2 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_2 rm2) (rmPrepared_1 rm2)))
            ) ;;;
        (not (rmCommitted_2 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_2 rm2) (rmCommitted_1 rm2)))
            ) ;;;
        (rmAborted_2 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_2 rm2) (rmAborted_1 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_2 rm2) (sentPrepared_1 rm2)))
        (= tmState_2 tmState_1)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 3
(declare-fun rmWorking_3 (RM) Bool)
(declare-fun rmPrepared_3 (RM) Bool)
(declare-fun rmCommitted_3 (RM) Bool)
(declare-fun rmAborted_3 (RM) Bool)
(declare-fun sentPrepared_3 (RM) Bool)
(declare-fun tmState_3 () TMState)

(declare-fun action_3 () Action)

; actions for frame 3
(assert (=> (= action_3 TMRcvPrepared) (and
    (= tmState_2 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_3 rmWorking_2)
    (forall ((rm RM)) (= (rmWorking_3 rm) (rmWorking_2 rm)))
    (forall ((rm RM)) (= (rmPrepared_3 rm) (rmPrepared_2 rm)))
    (forall ((rm RM)) (= (rmCommitted_3 rm) (rmCommitted_2 rm)))
    (forall ((rm RM)) (= (rmAborted_3 rm) (rmAborted_2 rm)))
    (forall ((rm RM)) (= (sentPrepared_3 rm) (sentPrepared_2 rm)))
    (= tmState_3 tmState_2)
))) ;;;

(assert (=> (= action_3 TMCommit) (and
    (= tmState_2 TMinit)
    (forall ((rm RM)) (sentPrepared_2 rm))
    (= tmState_3 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_3 rm) (rmWorking_2 rm)))
    (forall ((rm RM)) (= (rmPrepared_3 rm) (rmPrepared_2 rm)))
    (forall ((rm RM)) (= (rmCommitted_3 rm) (rmCommitted_2 rm)))
    (forall ((rm RM)) (= (rmAborted_3 rm) (rmAborted_2 rm)))
    (forall ((rm RM)) (= (sentPrepared_3 rm) (sentPrepared_2 rm)))
))) ;;;

(assert (=> (= action_3 TMAbort) (and
    (= tmState_2 TMinit)
    (= tmState_3 TMaborted)
    (forall ((rm RM)) (= (rmWorking_3 rm) (rmWorking_2 rm)))
    (forall ((rm RM)) (= (rmPrepared_3 rm) (rmPrepared_2 rm)))
    (forall ((rm RM)) (= (rmCommitted_3 rm) (rmCommitted_2 rm)))
    (forall ((rm RM)) (= (rmAborted_3 rm) (rmAborted_2 rm)))
    (forall ((rm RM)) (= (sentPrepared_3 rm) (sentPrepared_2 rm)))
))) ;;;

(assert (=> (= action_3 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_2 rm)
        (not (rmWorking_3 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_3 rm2) (rmWorking_2 rm2)))
            ) ;;;
        (rmPrepared_3 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_3 rm2) (rmPrepared_2 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_3 rm2) (sentPrepared_2 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_3 rm2) (rmCommitted_2 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_3 rm2) (rmAborted_2 rm2)))
        (= tmState_3 tmState_2)
)))) ;;;

(assert (=> (= action_3 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_2 rm)
        (not (rmWorking_3 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_3 rm2) (rmWorking_2 rm2)))
            ) ;;;
        (rmAborted_3 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_3 rm2) (rmAborted_2 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_3 rm2) (rmCommitted_2 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_3 rm2) (sentPrepared_2 rm2)))
        (= tmState_3 tmState_2)
)))) ;;;

(assert (=> (= action_3 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_2 TMcommitted)
        (not (rmWorking_3 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_3 rm2) (rmWorking_2 rm2)))
            ) ;;;
        (not (rmPrepared_3 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_3 rm2) (rmPrepared_2 rm2)))
            ) ;;;
        (rmCommitted_3 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_3 rm2) (rmCommitted_2 rm2)))
            ) ;;;
        (not (rmAborted_3 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_3 rm2) (rmAborted_2 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_3 rm2) (sentPrepared_2 rm2)))
        (= tmState_3 tmState_2)
)))) ;;;

(assert (=> (= action_3 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_2 TMaborted)
        (not (rmWorking_3 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_3 rm2) (rmWorking_2 rm2)))
            ) ;;;
        (not (rmPrepared_3 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_3 rm2) (rmPrepared_2 rm2)))
            ) ;;;
        (not (rmCommitted_3 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_3 rm2) (rmCommitted_2 rm2)))
            ) ;;;
        (rmAborted_3 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_3 rm2) (rmAborted_2 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_3 rm2) (sentPrepared_2 rm2)))
        (= tmState_3 tmState_2)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 4
(declare-fun rmWorking_4 (RM) Bool)
(declare-fun rmPrepared_4 (RM) Bool)
(declare-fun rmCommitted_4 (RM) Bool)
(declare-fun rmAborted_4 (RM) Bool)
(declare-fun sentPrepared_4 (RM) Bool)
(declare-fun tmState_4 () TMState)

(declare-fun action_4 () Action)

; actions for frame 4
(assert (=> (= action_4 TMRcvPrepared) (and
    (= tmState_3 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_4 rmWorking_3)
    (forall ((rm RM)) (= (rmWorking_4 rm) (rmWorking_3 rm)))
    (forall ((rm RM)) (= (rmPrepared_4 rm) (rmPrepared_3 rm)))
    (forall ((rm RM)) (= (rmCommitted_4 rm) (rmCommitted_3 rm)))
    (forall ((rm RM)) (= (rmAborted_4 rm) (rmAborted_3 rm)))
    (forall ((rm RM)) (= (sentPrepared_4 rm) (sentPrepared_3 rm)))
    (= tmState_4 tmState_3)
))) ;;;

(assert (=> (= action_4 TMCommit) (and
    (= tmState_3 TMinit)
    (forall ((rm RM)) (sentPrepared_3 rm))
    (= tmState_4 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_4 rm) (rmWorking_3 rm)))
    (forall ((rm RM)) (= (rmPrepared_4 rm) (rmPrepared_3 rm)))
    (forall ((rm RM)) (= (rmCommitted_4 rm) (rmCommitted_3 rm)))
    (forall ((rm RM)) (= (rmAborted_4 rm) (rmAborted_3 rm)))
    (forall ((rm RM)) (= (sentPrepared_4 rm) (sentPrepared_3 rm)))
))) ;;;

(assert (=> (= action_4 TMAbort) (and
    (= tmState_3 TMinit)
    (= tmState_4 TMaborted)
    (forall ((rm RM)) (= (rmWorking_4 rm) (rmWorking_3 rm)))
    (forall ((rm RM)) (= (rmPrepared_4 rm) (rmPrepared_3 rm)))
    (forall ((rm RM)) (= (rmCommitted_4 rm) (rmCommitted_3 rm)))
    (forall ((rm RM)) (= (rmAborted_4 rm) (rmAborted_3 rm)))
    (forall ((rm RM)) (= (sentPrepared_4 rm) (sentPrepared_3 rm)))
))) ;;;

(assert (=> (= action_4 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_3 rm)
        (not (rmWorking_4 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_4 rm2) (rmWorking_3 rm2)))
            ) ;;;
        (rmPrepared_4 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_4 rm2) (rmPrepared_3 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_4 rm2) (sentPrepared_3 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_4 rm2) (rmCommitted_3 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_4 rm2) (rmAborted_3 rm2)))
        (= tmState_4 tmState_3)
)))) ;;;

(assert (=> (= action_4 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_3 rm)
        (not (rmWorking_4 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_4 rm2) (rmWorking_3 rm2)))
            ) ;;;
        (rmAborted_4 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_4 rm2) (rmAborted_3 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_4 rm2) (rmCommitted_3 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_4 rm2) (sentPrepared_3 rm2)))
        (= tmState_4 tmState_3)
)))) ;;;

(assert (=> (= action_4 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_3 TMcommitted)
        (not (rmWorking_4 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_4 rm2) (rmWorking_3 rm2)))
            ) ;;;
        (not (rmPrepared_4 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_4 rm2) (rmPrepared_3 rm2)))
            ) ;;;
        (rmCommitted_4 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_4 rm2) (rmCommitted_3 rm2)))
            ) ;;;
        (not (rmAborted_4 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_4 rm2) (rmAborted_3 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_4 rm2) (sentPrepared_3 rm2)))
        (= tmState_4 tmState_3)
)))) ;;;

(assert (=> (= action_4 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_3 TMaborted)
        (not (rmWorking_4 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_4 rm2) (rmWorking_3 rm2)))
            ) ;;;
        (not (rmPrepared_4 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_4 rm2) (rmPrepared_3 rm2)))
            ) ;;;
        (not (rmCommitted_4 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_4 rm2) (rmCommitted_3 rm2)))
            ) ;;;
        (rmAborted_4 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_4 rm2) (rmAborted_3 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_4 rm2) (sentPrepared_3 rm2)))
        (= tmState_4 tmState_3)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 5
(declare-fun rmWorking_5 (RM) Bool)
(declare-fun rmPrepared_5 (RM) Bool)
(declare-fun rmCommitted_5 (RM) Bool)
(declare-fun rmAborted_5 (RM) Bool)
(declare-fun sentPrepared_5 (RM) Bool)
(declare-fun tmState_5 () TMState)

(declare-fun action_5 () Action)

; actions for frame 5
(assert (=> (= action_5 TMRcvPrepared) (and
    (= tmState_4 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_5 rmWorking_4)
    (forall ((rm RM)) (= (rmWorking_5 rm) (rmWorking_4 rm)))
    (forall ((rm RM)) (= (rmPrepared_5 rm) (rmPrepared_4 rm)))
    (forall ((rm RM)) (= (rmCommitted_5 rm) (rmCommitted_4 rm)))
    (forall ((rm RM)) (= (rmAborted_5 rm) (rmAborted_4 rm)))
    (forall ((rm RM)) (= (sentPrepared_5 rm) (sentPrepared_4 rm)))
    (= tmState_5 tmState_4)
))) ;;;

(assert (=> (= action_5 TMCommit) (and
    (= tmState_4 TMinit)
    (forall ((rm RM)) (sentPrepared_4 rm))
    (= tmState_5 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_5 rm) (rmWorking_4 rm)))
    (forall ((rm RM)) (= (rmPrepared_5 rm) (rmPrepared_4 rm)))
    (forall ((rm RM)) (= (rmCommitted_5 rm) (rmCommitted_4 rm)))
    (forall ((rm RM)) (= (rmAborted_5 rm) (rmAborted_4 rm)))
    (forall ((rm RM)) (= (sentPrepared_5 rm) (sentPrepared_4 rm)))
))) ;;;

(assert (=> (= action_5 TMAbort) (and
    (= tmState_4 TMinit)
    (= tmState_5 TMaborted)
    (forall ((rm RM)) (= (rmWorking_5 rm) (rmWorking_4 rm)))
    (forall ((rm RM)) (= (rmPrepared_5 rm) (rmPrepared_4 rm)))
    (forall ((rm RM)) (= (rmCommitted_5 rm) (rmCommitted_4 rm)))
    (forall ((rm RM)) (= (rmAborted_5 rm) (rmAborted_4 rm)))
    (forall ((rm RM)) (= (sentPrepared_5 rm) (sentPrepared_4 rm)))
))) ;;;

(assert (=> (= action_5 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_4 rm)
        (not (rmWorking_5 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_5 rm2) (rmWorking_4 rm2)))
            ) ;;;
        (rmPrepared_5 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_5 rm2) (rmPrepared_4 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_5 rm2) (sentPrepared_4 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_5 rm2) (rmCommitted_4 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_5 rm2) (rmAborted_4 rm2)))
        (= tmState_5 tmState_4)
)))) ;;;

(assert (=> (= action_5 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_4 rm)
        (not (rmWorking_5 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_5 rm2) (rmWorking_4 rm2)))
            ) ;;;
        (rmAborted_5 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_5 rm2) (rmAborted_4 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_5 rm2) (rmCommitted_4 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_5 rm2) (sentPrepared_4 rm2)))
        (= tmState_5 tmState_4)
)))) ;;;

(assert (=> (= action_5 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_4 TMcommitted)
        (not (rmWorking_5 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_5 rm2) (rmWorking_4 rm2)))
            ) ;;;
        (not (rmPrepared_5 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_5 rm2) (rmPrepared_4 rm2)))
            ) ;;;
        (rmCommitted_5 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_5 rm2) (rmCommitted_4 rm2)))
            ) ;;;
        (not (rmAborted_5 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_5 rm2) (rmAborted_4 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_5 rm2) (sentPrepared_4 rm2)))
        (= tmState_5 tmState_4)
)))) ;;;

(assert (=> (= action_5 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_4 TMaborted)
        (not (rmWorking_5 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_5 rm2) (rmWorking_4 rm2)))
            ) ;;;
        (not (rmPrepared_5 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_5 rm2) (rmPrepared_4 rm2)))
            ) ;;;
        (not (rmCommitted_5 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_5 rm2) (rmCommitted_4 rm2)))
            ) ;;;
        (rmAborted_5 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_5 rm2) (rmAborted_4 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_5 rm2) (sentPrepared_4 rm2)))
        (= tmState_5 tmState_4)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 6
(declare-fun rmWorking_6 (RM) Bool)
(declare-fun rmPrepared_6 (RM) Bool)
(declare-fun rmCommitted_6 (RM) Bool)
(declare-fun rmAborted_6 (RM) Bool)
(declare-fun sentPrepared_6 (RM) Bool)
(declare-fun tmState_6 () TMState)

(declare-fun action_6 () Action)

; actions for frame 6
(assert (=> (= action_6 TMRcvPrepared) (and
    (= tmState_5 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_6 rmWorking_5)
    (forall ((rm RM)) (= (rmWorking_6 rm) (rmWorking_5 rm)))
    (forall ((rm RM)) (= (rmPrepared_6 rm) (rmPrepared_5 rm)))
    (forall ((rm RM)) (= (rmCommitted_6 rm) (rmCommitted_5 rm)))
    (forall ((rm RM)) (= (rmAborted_6 rm) (rmAborted_5 rm)))
    (forall ((rm RM)) (= (sentPrepared_6 rm) (sentPrepared_5 rm)))
    (= tmState_6 tmState_5)
))) ;;;

(assert (=> (= action_6 TMCommit) (and
    (= tmState_5 TMinit)
    (forall ((rm RM)) (sentPrepared_5 rm))
    (= tmState_6 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_6 rm) (rmWorking_5 rm)))
    (forall ((rm RM)) (= (rmPrepared_6 rm) (rmPrepared_5 rm)))
    (forall ((rm RM)) (= (rmCommitted_6 rm) (rmCommitted_5 rm)))
    (forall ((rm RM)) (= (rmAborted_6 rm) (rmAborted_5 rm)))
    (forall ((rm RM)) (= (sentPrepared_6 rm) (sentPrepared_5 rm)))
))) ;;;

(assert (=> (= action_6 TMAbort) (and
    (= tmState_5 TMinit)
    (= tmState_6 TMaborted)
    (forall ((rm RM)) (= (rmWorking_6 rm) (rmWorking_5 rm)))
    (forall ((rm RM)) (= (rmPrepared_6 rm) (rmPrepared_5 rm)))
    (forall ((rm RM)) (= (rmCommitted_6 rm) (rmCommitted_5 rm)))
    (forall ((rm RM)) (= (rmAborted_6 rm) (rmAborted_5 rm)))
    (forall ((rm RM)) (= (sentPrepared_6 rm) (sentPrepared_5 rm)))
))) ;;;

(assert (=> (= action_6 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_5 rm)
        (not (rmWorking_6 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_6 rm2) (rmWorking_5 rm2)))
            ) ;;;
        (rmPrepared_6 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_6 rm2) (rmPrepared_5 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_6 rm2) (sentPrepared_5 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_6 rm2) (rmCommitted_5 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_6 rm2) (rmAborted_5 rm2)))
        (= tmState_6 tmState_5)
)))) ;;;

(assert (=> (= action_6 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_5 rm)
        (not (rmWorking_6 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_6 rm2) (rmWorking_5 rm2)))
            ) ;;;
        (rmAborted_6 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_6 rm2) (rmAborted_5 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_6 rm2) (rmCommitted_5 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_6 rm2) (sentPrepared_5 rm2)))
        (= tmState_6 tmState_5)
)))) ;;;

(assert (=> (= action_6 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_5 TMcommitted)
        (not (rmWorking_6 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_6 rm2) (rmWorking_5 rm2)))
            ) ;;;
        (not (rmPrepared_6 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_6 rm2) (rmPrepared_5 rm2)))
            ) ;;;
        (rmCommitted_6 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_6 rm2) (rmCommitted_5 rm2)))
            ) ;;;
        (not (rmAborted_6 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_6 rm2) (rmAborted_5 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_6 rm2) (sentPrepared_5 rm2)))
        (= tmState_6 tmState_5)
)))) ;;;

(assert (=> (= action_6 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_5 TMaborted)
        (not (rmWorking_6 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_6 rm2) (rmWorking_5 rm2)))
            ) ;;;
        (not (rmPrepared_6 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_6 rm2) (rmPrepared_5 rm2)))
            ) ;;;
        (not (rmCommitted_6 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_6 rm2) (rmCommitted_5 rm2)))
            ) ;;;
        (rmAborted_6 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_6 rm2) (rmAborted_5 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_6 rm2) (sentPrepared_5 rm2)))
        (= tmState_6 tmState_5)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 7
(declare-fun rmWorking_7 (RM) Bool)
(declare-fun rmPrepared_7 (RM) Bool)
(declare-fun rmCommitted_7 (RM) Bool)
(declare-fun rmAborted_7 (RM) Bool)
(declare-fun sentPrepared_7 (RM) Bool)
(declare-fun tmState_7 () TMState)

(declare-fun action_7 () Action)

; actions for frame 7
(assert (=> (= action_7 TMRcvPrepared) (and
    (= tmState_6 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_7 rmWorking_6)
    (forall ((rm RM)) (= (rmWorking_7 rm) (rmWorking_6 rm)))
    (forall ((rm RM)) (= (rmPrepared_7 rm) (rmPrepared_6 rm)))
    (forall ((rm RM)) (= (rmCommitted_7 rm) (rmCommitted_6 rm)))
    (forall ((rm RM)) (= (rmAborted_7 rm) (rmAborted_6 rm)))
    (forall ((rm RM)) (= (sentPrepared_7 rm) (sentPrepared_6 rm)))
    (= tmState_7 tmState_6)
))) ;;;

(assert (=> (= action_7 TMCommit) (and
    (= tmState_6 TMinit)
    (forall ((rm RM)) (sentPrepared_6 rm))
    (= tmState_7 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_7 rm) (rmWorking_6 rm)))
    (forall ((rm RM)) (= (rmPrepared_7 rm) (rmPrepared_6 rm)))
    (forall ((rm RM)) (= (rmCommitted_7 rm) (rmCommitted_6 rm)))
    (forall ((rm RM)) (= (rmAborted_7 rm) (rmAborted_6 rm)))
    (forall ((rm RM)) (= (sentPrepared_7 rm) (sentPrepared_6 rm)))
))) ;;;

(assert (=> (= action_7 TMAbort) (and
    (= tmState_6 TMinit)
    (= tmState_7 TMaborted)
    (forall ((rm RM)) (= (rmWorking_7 rm) (rmWorking_6 rm)))
    (forall ((rm RM)) (= (rmPrepared_7 rm) (rmPrepared_6 rm)))
    (forall ((rm RM)) (= (rmCommitted_7 rm) (rmCommitted_6 rm)))
    (forall ((rm RM)) (= (rmAborted_7 rm) (rmAborted_6 rm)))
    (forall ((rm RM)) (= (sentPrepared_7 rm) (sentPrepared_6 rm)))
))) ;;;

(assert (=> (= action_7 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_6 rm)
        (not (rmWorking_7 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_7 rm2) (rmWorking_6 rm2)))
            ) ;;;
        (rmPrepared_7 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_7 rm2) (rmPrepared_6 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_7 rm2) (sentPrepared_6 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_7 rm2) (rmCommitted_6 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_7 rm2) (rmAborted_6 rm2)))
        (= tmState_7 tmState_6)
)))) ;;;

(assert (=> (= action_7 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_6 rm)
        (not (rmWorking_7 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_7 rm2) (rmWorking_6 rm2)))
            ) ;;;
        (rmAborted_7 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_7 rm2) (rmAborted_6 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_7 rm2) (rmCommitted_6 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_7 rm2) (sentPrepared_6 rm2)))
        (= tmState_7 tmState_6)
)))) ;;;

(assert (=> (= action_7 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_6 TMcommitted)
        (not (rmWorking_7 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_7 rm2) (rmWorking_6 rm2)))
            ) ;;;
        (not (rmPrepared_7 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_7 rm2) (rmPrepared_6 rm2)))
            ) ;;;
        (rmCommitted_7 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_7 rm2) (rmCommitted_6 rm2)))
            ) ;;;
        (not (rmAborted_7 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_7 rm2) (rmAborted_6 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_7 rm2) (sentPrepared_6 rm2)))
        (= tmState_7 tmState_6)
)))) ;;;

(assert (=> (= action_7 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_6 TMaborted)
        (not (rmWorking_7 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_7 rm2) (rmWorking_6 rm2)))
            ) ;;;
        (not (rmPrepared_7 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_7 rm2) (rmPrepared_6 rm2)))
            ) ;;;
        (not (rmCommitted_7 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_7 rm2) (rmCommitted_6 rm2)))
            ) ;;;
        (rmAborted_7 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_7 rm2) (rmAborted_6 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_7 rm2) (sentPrepared_6 rm2)))
        (= tmState_7 tmState_6)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 8
(declare-fun rmWorking_8 (RM) Bool)
(declare-fun rmPrepared_8 (RM) Bool)
(declare-fun rmCommitted_8 (RM) Bool)
(declare-fun rmAborted_8 (RM) Bool)
(declare-fun sentPrepared_8 (RM) Bool)
(declare-fun tmState_8 () TMState)

(declare-fun action_8 () Action)

; actions for frame 8
(assert (=> (= action_8 TMRcvPrepared) (and
    (= tmState_7 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_8 rmWorking_7)
    (forall ((rm RM)) (= (rmWorking_8 rm) (rmWorking_7 rm)))
    (forall ((rm RM)) (= (rmPrepared_8 rm) (rmPrepared_7 rm)))
    (forall ((rm RM)) (= (rmCommitted_8 rm) (rmCommitted_7 rm)))
    (forall ((rm RM)) (= (rmAborted_8 rm) (rmAborted_7 rm)))
    (forall ((rm RM)) (= (sentPrepared_8 rm) (sentPrepared_7 rm)))
    (= tmState_8 tmState_7)
))) ;;;

(assert (=> (= action_8 TMCommit) (and
    (= tmState_7 TMinit)
    (forall ((rm RM)) (sentPrepared_7 rm))
    (= tmState_8 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_8 rm) (rmWorking_7 rm)))
    (forall ((rm RM)) (= (rmPrepared_8 rm) (rmPrepared_7 rm)))
    (forall ((rm RM)) (= (rmCommitted_8 rm) (rmCommitted_7 rm)))
    (forall ((rm RM)) (= (rmAborted_8 rm) (rmAborted_7 rm)))
    (forall ((rm RM)) (= (sentPrepared_8 rm) (sentPrepared_7 rm)))
))) ;;;

(assert (=> (= action_8 TMAbort) (and
    (= tmState_7 TMinit)
    (= tmState_8 TMaborted)
    (forall ((rm RM)) (= (rmWorking_8 rm) (rmWorking_7 rm)))
    (forall ((rm RM)) (= (rmPrepared_8 rm) (rmPrepared_7 rm)))
    (forall ((rm RM)) (= (rmCommitted_8 rm) (rmCommitted_7 rm)))
    (forall ((rm RM)) (= (rmAborted_8 rm) (rmAborted_7 rm)))
    (forall ((rm RM)) (= (sentPrepared_8 rm) (sentPrepared_7 rm)))
))) ;;;

(assert (=> (= action_8 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_7 rm)
        (not (rmWorking_8 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_8 rm2) (rmWorking_7 rm2)))
            ) ;;;
        (rmPrepared_8 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_8 rm2) (rmPrepared_7 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_8 rm2) (sentPrepared_7 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_8 rm2) (rmCommitted_7 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_8 rm2) (rmAborted_7 rm2)))
        (= tmState_8 tmState_7)
)))) ;;;

(assert (=> (= action_8 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_7 rm)
        (not (rmWorking_8 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_8 rm2) (rmWorking_7 rm2)))
            ) ;;;
        (rmAborted_8 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_8 rm2) (rmAborted_7 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_8 rm2) (rmCommitted_7 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_8 rm2) (sentPrepared_7 rm2)))
        (= tmState_8 tmState_7)
)))) ;;;

(assert (=> (= action_8 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_7 TMcommitted)
        (not (rmWorking_8 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_8 rm2) (rmWorking_7 rm2)))
            ) ;;;
        (not (rmPrepared_8 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_8 rm2) (rmPrepared_7 rm2)))
            ) ;;;
        (rmCommitted_8 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_8 rm2) (rmCommitted_7 rm2)))
            ) ;;;
        (not (rmAborted_8 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_8 rm2) (rmAborted_7 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_8 rm2) (sentPrepared_7 rm2)))
        (= tmState_8 tmState_7)
)))) ;;;

(assert (=> (= action_8 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_7 TMaborted)
        (not (rmWorking_8 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_8 rm2) (rmWorking_7 rm2)))
            ) ;;;
        (not (rmPrepared_8 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_8 rm2) (rmPrepared_7 rm2)))
            ) ;;;
        (not (rmCommitted_8 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_8 rm2) (rmCommitted_7 rm2)))
            ) ;;;
        (rmAborted_8 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_8 rm2) (rmAborted_7 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_8 rm2) (sentPrepared_7 rm2)))
        (= tmState_8 tmState_7)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 9
(declare-fun rmWorking_9 (RM) Bool)
(declare-fun rmPrepared_9 (RM) Bool)
(declare-fun rmCommitted_9 (RM) Bool)
(declare-fun rmAborted_9 (RM) Bool)
(declare-fun sentPrepared_9 (RM) Bool)
(declare-fun tmState_9 () TMState)

(declare-fun action_9 () Action)

; actions for frame 9
(assert (=> (= action_9 TMRcvPrepared) (and
    (= tmState_8 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_9 rmWorking_8)
    (forall ((rm RM)) (= (rmWorking_9 rm) (rmWorking_8 rm)))
    (forall ((rm RM)) (= (rmPrepared_9 rm) (rmPrepared_8 rm)))
    (forall ((rm RM)) (= (rmCommitted_9 rm) (rmCommitted_8 rm)))
    (forall ((rm RM)) (= (rmAborted_9 rm) (rmAborted_8 rm)))
    (forall ((rm RM)) (= (sentPrepared_9 rm) (sentPrepared_8 rm)))
    (= tmState_9 tmState_8)
))) ;;;

(assert (=> (= action_9 TMCommit) (and
    (= tmState_8 TMinit)
    (forall ((rm RM)) (sentPrepared_8 rm))
    (= tmState_9 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_9 rm) (rmWorking_8 rm)))
    (forall ((rm RM)) (= (rmPrepared_9 rm) (rmPrepared_8 rm)))
    (forall ((rm RM)) (= (rmCommitted_9 rm) (rmCommitted_8 rm)))
    (forall ((rm RM)) (= (rmAborted_9 rm) (rmAborted_8 rm)))
    (forall ((rm RM)) (= (sentPrepared_9 rm) (sentPrepared_8 rm)))
))) ;;;

(assert (=> (= action_9 TMAbort) (and
    (= tmState_8 TMinit)
    (= tmState_9 TMaborted)
    (forall ((rm RM)) (= (rmWorking_9 rm) (rmWorking_8 rm)))
    (forall ((rm RM)) (= (rmPrepared_9 rm) (rmPrepared_8 rm)))
    (forall ((rm RM)) (= (rmCommitted_9 rm) (rmCommitted_8 rm)))
    (forall ((rm RM)) (= (rmAborted_9 rm) (rmAborted_8 rm)))
    (forall ((rm RM)) (= (sentPrepared_9 rm) (sentPrepared_8 rm)))
))) ;;;

(assert (=> (= action_9 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_8 rm)
        (not (rmWorking_9 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_9 rm2) (rmWorking_8 rm2)))
            ) ;;;
        (rmPrepared_9 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_9 rm2) (rmPrepared_8 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_9 rm2) (sentPrepared_8 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_9 rm2) (rmCommitted_8 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_9 rm2) (rmAborted_8 rm2)))
        (= tmState_9 tmState_8)
)))) ;;;

(assert (=> (= action_9 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_8 rm)
        (not (rmWorking_9 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_9 rm2) (rmWorking_8 rm2)))
            ) ;;;
        (rmAborted_9 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_9 rm2) (rmAborted_8 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_9 rm2) (rmCommitted_8 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_9 rm2) (sentPrepared_8 rm2)))
        (= tmState_9 tmState_8)
)))) ;;;

(assert (=> (= action_9 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_8 TMcommitted)
        (not (rmWorking_9 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_9 rm2) (rmWorking_8 rm2)))
            ) ;;;
        (not (rmPrepared_9 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_9 rm2) (rmPrepared_8 rm2)))
            ) ;;;
        (rmCommitted_9 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_9 rm2) (rmCommitted_8 rm2)))
            ) ;;;
        (not (rmAborted_9 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_9 rm2) (rmAborted_8 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_9 rm2) (sentPrepared_8 rm2)))
        (= tmState_9 tmState_8)
)))) ;;;

(assert (=> (= action_9 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_8 TMaborted)
        (not (rmWorking_9 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_9 rm2) (rmWorking_8 rm2)))
            ) ;;;
        (not (rmPrepared_9 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_9 rm2) (rmPrepared_8 rm2)))
            ) ;;;
        (not (rmCommitted_9 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_9 rm2) (rmCommitted_8 rm2)))
            ) ;;;
        (rmAborted_9 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_9 rm2) (rmAborted_8 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_9 rm2) (sentPrepared_8 rm2)))
        (= tmState_9 tmState_8)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 10
(declare-fun rmWorking_10 (RM) Bool)
(declare-fun rmPrepared_10 (RM) Bool)
(declare-fun rmCommitted_10 (RM) Bool)
(declare-fun rmAborted_10 (RM) Bool)
(declare-fun sentPrepared_10 (RM) Bool)
(declare-fun tmState_10 () TMState)

(declare-fun action_10 () Action)

; actions for frame 10
(assert (=> (= action_10 TMRcvPrepared) (and
    (= tmState_9 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_10 rmWorking_9)
    (forall ((rm RM)) (= (rmWorking_10 rm) (rmWorking_9 rm)))
    (forall ((rm RM)) (= (rmPrepared_10 rm) (rmPrepared_9 rm)))
    (forall ((rm RM)) (= (rmCommitted_10 rm) (rmCommitted_9 rm)))
    (forall ((rm RM)) (= (rmAborted_10 rm) (rmAborted_9 rm)))
    (forall ((rm RM)) (= (sentPrepared_10 rm) (sentPrepared_9 rm)))
    (= tmState_10 tmState_9)
))) ;;;

(assert (=> (= action_10 TMCommit) (and
    (= tmState_9 TMinit)
    (forall ((rm RM)) (sentPrepared_9 rm))
    (= tmState_10 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_10 rm) (rmWorking_9 rm)))
    (forall ((rm RM)) (= (rmPrepared_10 rm) (rmPrepared_9 rm)))
    (forall ((rm RM)) (= (rmCommitted_10 rm) (rmCommitted_9 rm)))
    (forall ((rm RM)) (= (rmAborted_10 rm) (rmAborted_9 rm)))
    (forall ((rm RM)) (= (sentPrepared_10 rm) (sentPrepared_9 rm)))
))) ;;;

(assert (=> (= action_10 TMAbort) (and
    (= tmState_9 TMinit)
    (= tmState_10 TMaborted)
    (forall ((rm RM)) (= (rmWorking_10 rm) (rmWorking_9 rm)))
    (forall ((rm RM)) (= (rmPrepared_10 rm) (rmPrepared_9 rm)))
    (forall ((rm RM)) (= (rmCommitted_10 rm) (rmCommitted_9 rm)))
    (forall ((rm RM)) (= (rmAborted_10 rm) (rmAborted_9 rm)))
    (forall ((rm RM)) (= (sentPrepared_10 rm) (sentPrepared_9 rm)))
))) ;;;

(assert (=> (= action_10 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_9 rm)
        (not (rmWorking_10 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_10 rm2) (rmWorking_9 rm2)))
            ) ;;;
        (rmPrepared_10 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_10 rm2) (rmPrepared_9 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_10 rm2) (sentPrepared_9 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_10 rm2) (rmCommitted_9 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_10 rm2) (rmAborted_9 rm2)))
        (= tmState_10 tmState_9)
)))) ;;;

(assert (=> (= action_10 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_9 rm)
        (not (rmWorking_10 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_10 rm2) (rmWorking_9 rm2)))
            ) ;;;
        (rmAborted_10 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_10 rm2) (rmAborted_9 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_10 rm2) (rmCommitted_9 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_10 rm2) (sentPrepared_9 rm2)))
        (= tmState_10 tmState_9)
)))) ;;;

(assert (=> (= action_10 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_9 TMcommitted)
        (not (rmWorking_10 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_10 rm2) (rmWorking_9 rm2)))
            ) ;;;
        (not (rmPrepared_10 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_10 rm2) (rmPrepared_9 rm2)))
            ) ;;;
        (rmCommitted_10 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_10 rm2) (rmCommitted_9 rm2)))
            ) ;;;
        (not (rmAborted_10 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_10 rm2) (rmAborted_9 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_10 rm2) (sentPrepared_9 rm2)))
        (= tmState_10 tmState_9)
)))) ;;;

(assert (=> (= action_10 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_9 TMaborted)
        (not (rmWorking_10 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_10 rm2) (rmWorking_9 rm2)))
            ) ;;;
        (not (rmPrepared_10 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_10 rm2) (rmPrepared_9 rm2)))
            ) ;;;
        (not (rmCommitted_10 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_10 rm2) (rmCommitted_9 rm2)))
            ) ;;;
        (rmAborted_10 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_10 rm2) (rmAborted_9 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_10 rm2) (sentPrepared_9 rm2)))
        (= tmState_10 tmState_9)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 11
(declare-fun rmWorking_11 (RM) Bool)
(declare-fun rmPrepared_11 (RM) Bool)
(declare-fun rmCommitted_11 (RM) Bool)
(declare-fun rmAborted_11 (RM) Bool)
(declare-fun sentPrepared_11 (RM) Bool)
(declare-fun tmState_11 () TMState)

(declare-fun action_11 () Action)

; actions for frame 11
(assert (=> (= action_11 TMRcvPrepared) (and
    (= tmState_10 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_11 rmWorking_10)
    (forall ((rm RM)) (= (rmWorking_11 rm) (rmWorking_10 rm)))
    (forall ((rm RM)) (= (rmPrepared_11 rm) (rmPrepared_10 rm)))
    (forall ((rm RM)) (= (rmCommitted_11 rm) (rmCommitted_10 rm)))
    (forall ((rm RM)) (= (rmAborted_11 rm) (rmAborted_10 rm)))
    (forall ((rm RM)) (= (sentPrepared_11 rm) (sentPrepared_10 rm)))
    (= tmState_11 tmState_10)
))) ;;;

(assert (=> (= action_11 TMCommit) (and
    (= tmState_10 TMinit)
    (forall ((rm RM)) (sentPrepared_10 rm))
    (= tmState_11 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_11 rm) (rmWorking_10 rm)))
    (forall ((rm RM)) (= (rmPrepared_11 rm) (rmPrepared_10 rm)))
    (forall ((rm RM)) (= (rmCommitted_11 rm) (rmCommitted_10 rm)))
    (forall ((rm RM)) (= (rmAborted_11 rm) (rmAborted_10 rm)))
    (forall ((rm RM)) (= (sentPrepared_11 rm) (sentPrepared_10 rm)))
))) ;;;

(assert (=> (= action_11 TMAbort) (and
    (= tmState_10 TMinit)
    (= tmState_11 TMaborted)
    (forall ((rm RM)) (= (rmWorking_11 rm) (rmWorking_10 rm)))
    (forall ((rm RM)) (= (rmPrepared_11 rm) (rmPrepared_10 rm)))
    (forall ((rm RM)) (= (rmCommitted_11 rm) (rmCommitted_10 rm)))
    (forall ((rm RM)) (= (rmAborted_11 rm) (rmAborted_10 rm)))
    (forall ((rm RM)) (= (sentPrepared_11 rm) (sentPrepared_10 rm)))
))) ;;;

(assert (=> (= action_11 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_10 rm)
        (not (rmWorking_11 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_11 rm2) (rmWorking_10 rm2)))
            ) ;;;
        (rmPrepared_11 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_11 rm2) (rmPrepared_10 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_11 rm2) (sentPrepared_10 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_11 rm2) (rmCommitted_10 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_11 rm2) (rmAborted_10 rm2)))
        (= tmState_11 tmState_10)
)))) ;;;

(assert (=> (= action_11 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_10 rm)
        (not (rmWorking_11 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_11 rm2) (rmWorking_10 rm2)))
            ) ;;;
        (rmAborted_11 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_11 rm2) (rmAborted_10 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_11 rm2) (rmCommitted_10 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_11 rm2) (sentPrepared_10 rm2)))
        (= tmState_11 tmState_10)
)))) ;;;

(assert (=> (= action_11 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_10 TMcommitted)
        (not (rmWorking_11 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_11 rm2) (rmWorking_10 rm2)))
            ) ;;;
        (not (rmPrepared_11 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_11 rm2) (rmPrepared_10 rm2)))
            ) ;;;
        (rmCommitted_11 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_11 rm2) (rmCommitted_10 rm2)))
            ) ;;;
        (not (rmAborted_11 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_11 rm2) (rmAborted_10 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_11 rm2) (sentPrepared_10 rm2)))
        (= tmState_11 tmState_10)
)))) ;;;

(assert (=> (= action_11 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_10 TMaborted)
        (not (rmWorking_11 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_11 rm2) (rmWorking_10 rm2)))
            ) ;;;
        (not (rmPrepared_11 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_11 rm2) (rmPrepared_10 rm2)))
            ) ;;;
        (not (rmCommitted_11 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_11 rm2) (rmCommitted_10 rm2)))
            ) ;;;
        (rmAborted_11 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_11 rm2) (rmAborted_10 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_11 rm2) (sentPrepared_10 rm2)))
        (= tmState_11 tmState_10)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 12
(declare-fun rmWorking_12 (RM) Bool)
(declare-fun rmPrepared_12 (RM) Bool)
(declare-fun rmCommitted_12 (RM) Bool)
(declare-fun rmAborted_12 (RM) Bool)
(declare-fun sentPrepared_12 (RM) Bool)
(declare-fun tmState_12 () TMState)

(declare-fun action_12 () Action)

; actions for frame 12
(assert (=> (= action_12 TMRcvPrepared) (and
    (= tmState_11 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_12 rmWorking_11)
    (forall ((rm RM)) (= (rmWorking_12 rm) (rmWorking_11 rm)))
    (forall ((rm RM)) (= (rmPrepared_12 rm) (rmPrepared_11 rm)))
    (forall ((rm RM)) (= (rmCommitted_12 rm) (rmCommitted_11 rm)))
    (forall ((rm RM)) (= (rmAborted_12 rm) (rmAborted_11 rm)))
    (forall ((rm RM)) (= (sentPrepared_12 rm) (sentPrepared_11 rm)))
    (= tmState_12 tmState_11)
))) ;;;

(assert (=> (= action_12 TMCommit) (and
    (= tmState_11 TMinit)
    (forall ((rm RM)) (sentPrepared_11 rm))
    (= tmState_12 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_12 rm) (rmWorking_11 rm)))
    (forall ((rm RM)) (= (rmPrepared_12 rm) (rmPrepared_11 rm)))
    (forall ((rm RM)) (= (rmCommitted_12 rm) (rmCommitted_11 rm)))
    (forall ((rm RM)) (= (rmAborted_12 rm) (rmAborted_11 rm)))
    (forall ((rm RM)) (= (sentPrepared_12 rm) (sentPrepared_11 rm)))
))) ;;;

(assert (=> (= action_12 TMAbort) (and
    (= tmState_11 TMinit)
    (= tmState_12 TMaborted)
    (forall ((rm RM)) (= (rmWorking_12 rm) (rmWorking_11 rm)))
    (forall ((rm RM)) (= (rmPrepared_12 rm) (rmPrepared_11 rm)))
    (forall ((rm RM)) (= (rmCommitted_12 rm) (rmCommitted_11 rm)))
    (forall ((rm RM)) (= (rmAborted_12 rm) (rmAborted_11 rm)))
    (forall ((rm RM)) (= (sentPrepared_12 rm) (sentPrepared_11 rm)))
))) ;;;

(assert (=> (= action_12 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_11 rm)
        (not (rmWorking_12 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_12 rm2) (rmWorking_11 rm2)))
            ) ;;;
        (rmPrepared_12 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_12 rm2) (rmPrepared_11 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_12 rm2) (sentPrepared_11 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_12 rm2) (rmCommitted_11 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_12 rm2) (rmAborted_11 rm2)))
        (= tmState_12 tmState_11)
)))) ;;;

(assert (=> (= action_12 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_11 rm)
        (not (rmWorking_12 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_12 rm2) (rmWorking_11 rm2)))
            ) ;;;
        (rmAborted_12 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_12 rm2) (rmAborted_11 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_12 rm2) (rmCommitted_11 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_12 rm2) (sentPrepared_11 rm2)))
        (= tmState_12 tmState_11)
)))) ;;;

(assert (=> (= action_12 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_11 TMcommitted)
        (not (rmWorking_12 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_12 rm2) (rmWorking_11 rm2)))
            ) ;;;
        (not (rmPrepared_12 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_12 rm2) (rmPrepared_11 rm2)))
            ) ;;;
        (rmCommitted_12 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_12 rm2) (rmCommitted_11 rm2)))
            ) ;;;
        (not (rmAborted_12 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_12 rm2) (rmAborted_11 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_12 rm2) (sentPrepared_11 rm2)))
        (= tmState_12 tmState_11)
)))) ;;;

(assert (=> (= action_12 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_11 TMaborted)
        (not (rmWorking_12 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_12 rm2) (rmWorking_11 rm2)))
            ) ;;;
        (not (rmPrepared_12 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_12 rm2) (rmPrepared_11 rm2)))
            ) ;;;
        (not (rmCommitted_12 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_12 rm2) (rmCommitted_11 rm2)))
            ) ;;;
        (rmAborted_12 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_12 rm2) (rmAborted_11 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_12 rm2) (sentPrepared_11 rm2)))
        (= tmState_12 tmState_11)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 13
(declare-fun rmWorking_13 (RM) Bool)
(declare-fun rmPrepared_13 (RM) Bool)
(declare-fun rmCommitted_13 (RM) Bool)
(declare-fun rmAborted_13 (RM) Bool)
(declare-fun sentPrepared_13 (RM) Bool)
(declare-fun tmState_13 () TMState)

(declare-fun action_13 () Action)

; actions for frame 13
(assert (=> (= action_13 TMRcvPrepared) (and
    (= tmState_12 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_13 rmWorking_12)
    (forall ((rm RM)) (= (rmWorking_13 rm) (rmWorking_12 rm)))
    (forall ((rm RM)) (= (rmPrepared_13 rm) (rmPrepared_12 rm)))
    (forall ((rm RM)) (= (rmCommitted_13 rm) (rmCommitted_12 rm)))
    (forall ((rm RM)) (= (rmAborted_13 rm) (rmAborted_12 rm)))
    (forall ((rm RM)) (= (sentPrepared_13 rm) (sentPrepared_12 rm)))
    (= tmState_13 tmState_12)
))) ;;;

(assert (=> (= action_13 TMCommit) (and
    (= tmState_12 TMinit)
    (forall ((rm RM)) (sentPrepared_12 rm))
    (= tmState_13 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_13 rm) (rmWorking_12 rm)))
    (forall ((rm RM)) (= (rmPrepared_13 rm) (rmPrepared_12 rm)))
    (forall ((rm RM)) (= (rmCommitted_13 rm) (rmCommitted_12 rm)))
    (forall ((rm RM)) (= (rmAborted_13 rm) (rmAborted_12 rm)))
    (forall ((rm RM)) (= (sentPrepared_13 rm) (sentPrepared_12 rm)))
))) ;;;

(assert (=> (= action_13 TMAbort) (and
    (= tmState_12 TMinit)
    (= tmState_13 TMaborted)
    (forall ((rm RM)) (= (rmWorking_13 rm) (rmWorking_12 rm)))
    (forall ((rm RM)) (= (rmPrepared_13 rm) (rmPrepared_12 rm)))
    (forall ((rm RM)) (= (rmCommitted_13 rm) (rmCommitted_12 rm)))
    (forall ((rm RM)) (= (rmAborted_13 rm) (rmAborted_12 rm)))
    (forall ((rm RM)) (= (sentPrepared_13 rm) (sentPrepared_12 rm)))
))) ;;;

(assert (=> (= action_13 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_12 rm)
        (not (rmWorking_13 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_13 rm2) (rmWorking_12 rm2)))
            ) ;;;
        (rmPrepared_13 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_13 rm2) (rmPrepared_12 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_13 rm2) (sentPrepared_12 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_13 rm2) (rmCommitted_12 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_13 rm2) (rmAborted_12 rm2)))
        (= tmState_13 tmState_12)
)))) ;;;

(assert (=> (= action_13 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_12 rm)
        (not (rmWorking_13 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_13 rm2) (rmWorking_12 rm2)))
            ) ;;;
        (rmAborted_13 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_13 rm2) (rmAborted_12 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_13 rm2) (rmCommitted_12 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_13 rm2) (sentPrepared_12 rm2)))
        (= tmState_13 tmState_12)
)))) ;;;

(assert (=> (= action_13 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_12 TMcommitted)
        (not (rmWorking_13 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_13 rm2) (rmWorking_12 rm2)))
            ) ;;;
        (not (rmPrepared_13 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_13 rm2) (rmPrepared_12 rm2)))
            ) ;;;
        (rmCommitted_13 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_13 rm2) (rmCommitted_12 rm2)))
            ) ;;;
        (not (rmAborted_13 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_13 rm2) (rmAborted_12 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_13 rm2) (sentPrepared_12 rm2)))
        (= tmState_13 tmState_12)
)))) ;;;

(assert (=> (= action_13 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_12 TMaborted)
        (not (rmWorking_13 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_13 rm2) (rmWorking_12 rm2)))
            ) ;;;
        (not (rmPrepared_13 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_13 rm2) (rmPrepared_12 rm2)))
            ) ;;;
        (not (rmCommitted_13 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_13 rm2) (rmCommitted_12 rm2)))
            ) ;;;
        (rmAborted_13 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_13 rm2) (rmAborted_12 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_13 rm2) (sentPrepared_12 rm2)))
        (= tmState_13 tmState_12)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 14
(declare-fun rmWorking_14 (RM) Bool)
(declare-fun rmPrepared_14 (RM) Bool)
(declare-fun rmCommitted_14 (RM) Bool)
(declare-fun rmAborted_14 (RM) Bool)
(declare-fun sentPrepared_14 (RM) Bool)
(declare-fun tmState_14 () TMState)

(declare-fun action_14 () Action)

; actions for frame 14
(assert (=> (= action_14 TMRcvPrepared) (and
    (= tmState_13 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_14 rmWorking_13)
    (forall ((rm RM)) (= (rmWorking_14 rm) (rmWorking_13 rm)))
    (forall ((rm RM)) (= (rmPrepared_14 rm) (rmPrepared_13 rm)))
    (forall ((rm RM)) (= (rmCommitted_14 rm) (rmCommitted_13 rm)))
    (forall ((rm RM)) (= (rmAborted_14 rm) (rmAborted_13 rm)))
    (forall ((rm RM)) (= (sentPrepared_14 rm) (sentPrepared_13 rm)))
    (= tmState_14 tmState_13)
))) ;;;

(assert (=> (= action_14 TMCommit) (and
    (= tmState_13 TMinit)
    (forall ((rm RM)) (sentPrepared_13 rm))
    (= tmState_14 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_14 rm) (rmWorking_13 rm)))
    (forall ((rm RM)) (= (rmPrepared_14 rm) (rmPrepared_13 rm)))
    (forall ((rm RM)) (= (rmCommitted_14 rm) (rmCommitted_13 rm)))
    (forall ((rm RM)) (= (rmAborted_14 rm) (rmAborted_13 rm)))
    (forall ((rm RM)) (= (sentPrepared_14 rm) (sentPrepared_13 rm)))
))) ;;;

(assert (=> (= action_14 TMAbort) (and
    (= tmState_13 TMinit)
    (= tmState_14 TMaborted)
    (forall ((rm RM)) (= (rmWorking_14 rm) (rmWorking_13 rm)))
    (forall ((rm RM)) (= (rmPrepared_14 rm) (rmPrepared_13 rm)))
    (forall ((rm RM)) (= (rmCommitted_14 rm) (rmCommitted_13 rm)))
    (forall ((rm RM)) (= (rmAborted_14 rm) (rmAborted_13 rm)))
    (forall ((rm RM)) (= (sentPrepared_14 rm) (sentPrepared_13 rm)))
))) ;;;

(assert (=> (= action_14 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_13 rm)
        (not (rmWorking_14 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_14 rm2) (rmWorking_13 rm2)))
            ) ;;;
        (rmPrepared_14 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_14 rm2) (rmPrepared_13 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_14 rm2) (sentPrepared_13 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_14 rm2) (rmCommitted_13 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_14 rm2) (rmAborted_13 rm2)))
        (= tmState_14 tmState_13)
)))) ;;;

(assert (=> (= action_14 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_13 rm)
        (not (rmWorking_14 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_14 rm2) (rmWorking_13 rm2)))
            ) ;;;
        (rmAborted_14 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_14 rm2) (rmAborted_13 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_14 rm2) (rmCommitted_13 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_14 rm2) (sentPrepared_13 rm2)))
        (= tmState_14 tmState_13)
)))) ;;;

(assert (=> (= action_14 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_13 TMcommitted)
        (not (rmWorking_14 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_14 rm2) (rmWorking_13 rm2)))
            ) ;;;
        (not (rmPrepared_14 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_14 rm2) (rmPrepared_13 rm2)))
            ) ;;;
        (rmCommitted_14 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_14 rm2) (rmCommitted_13 rm2)))
            ) ;;;
        (not (rmAborted_14 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_14 rm2) (rmAborted_13 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_14 rm2) (sentPrepared_13 rm2)))
        (= tmState_14 tmState_13)
)))) ;;;

(assert (=> (= action_14 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_13 TMaborted)
        (not (rmWorking_14 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_14 rm2) (rmWorking_13 rm2)))
            ) ;;;
        (not (rmPrepared_14 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_14 rm2) (rmPrepared_13 rm2)))
            ) ;;;
        (not (rmCommitted_14 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_14 rm2) (rmCommitted_13 rm2)))
            ) ;;;
        (rmAborted_14 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_14 rm2) (rmAborted_13 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_14 rm2) (sentPrepared_13 rm2)))
        (= tmState_14 tmState_13)
)))) ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; frame 15
(declare-fun rmWorking_15 (RM) Bool)
(declare-fun rmPrepared_15 (RM) Bool)
(declare-fun rmCommitted_15 (RM) Bool)
(declare-fun rmAborted_15 (RM) Bool)
(declare-fun sentPrepared_15 (RM) Bool)
(declare-fun tmState_15 () TMState)

(declare-fun action_15 () Action)

; actions for frame 15
(assert (=> (= action_15 TMRcvPrepared) (and
    (= tmState_14 TMinit)
    ;; the line below gives us unknown:
    ;;(= rmWorking_15 rmWorking_14)
    (forall ((rm RM)) (= (rmWorking_15 rm) (rmWorking_14 rm)))
    (forall ((rm RM)) (= (rmPrepared_15 rm) (rmPrepared_14 rm)))
    (forall ((rm RM)) (= (rmCommitted_15 rm) (rmCommitted_14 rm)))
    (forall ((rm RM)) (= (rmAborted_15 rm) (rmAborted_14 rm)))
    (forall ((rm RM)) (= (sentPrepared_15 rm) (sentPrepared_14 rm)))
    (= tmState_15 tmState_14)
))) ;;;

(assert (=> (= action_15 TMCommit) (and
    (= tmState_14 TMinit)
    (forall ((rm RM)) (sentPrepared_14 rm))
    (= tmState_15 TMcommitted)
    (forall ((rm RM)) (= (rmWorking_15 rm) (rmWorking_14 rm)))
    (forall ((rm RM)) (= (rmPrepared_15 rm) (rmPrepared_14 rm)))
    (forall ((rm RM)) (= (rmCommitted_15 rm) (rmCommitted_14 rm)))
    (forall ((rm RM)) (= (rmAborted_15 rm) (rmAborted_14 rm)))
    (forall ((rm RM)) (= (sentPrepared_15 rm) (sentPrepared_14 rm)))
))) ;;;

(assert (=> (= action_15 TMAbort) (and
    (= tmState_14 TMinit)
    (= tmState_15 TMaborted)
    (forall ((rm RM)) (= (rmWorking_15 rm) (rmWorking_14 rm)))
    (forall ((rm RM)) (= (rmPrepared_15 rm) (rmPrepared_14 rm)))
    (forall ((rm RM)) (= (rmCommitted_15 rm) (rmCommitted_14 rm)))
    (forall ((rm RM)) (= (rmAborted_15 rm) (rmAborted_14 rm)))
    (forall ((rm RM)) (= (sentPrepared_15 rm) (sentPrepared_14 rm)))
))) ;;;

(assert (=> (= action_15 RMPrepare)
    (exists ((rm RM)) (and
        (rmWorking_14 rm)
        (not (rmWorking_15 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_15 rm2) (rmWorking_14 rm2)))
            ) ;;;
        (rmPrepared_15 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_15 rm2) (rmPrepared_14 rm2)))
            ) ;;;
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (sentPrepared_15 rm2) (sentPrepared_14 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_15 rm2) (rmCommitted_14 rm2)))
        (forall ((rm2 RM)) (= (rmAborted_15 rm2) (rmAborted_14 rm2)))
        (= tmState_15 tmState_14)
)))) ;;;

(assert (=> (= action_15 RMChooseToAbort)
    (exists ((rm RM)) (and
        (rmWorking_14 rm)
        (not (rmWorking_15 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_15 rm2) (rmWorking_14 rm2)))
            ) ;;;
        (rmAborted_15 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_15 rm2) (rmAborted_14 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (rmCommitted_15 rm2) (rmCommitted_14 rm2)))
        (forall ((rm2 RM)) (= (sentPrepared_15 rm2) (sentPrepared_14 rm2)))
        (= tmState_15 tmState_14)
)))) ;;;

(assert (=> (= action_15 RMRcvCommitMsg)
    (exists ((rm RM)) (and
        (= tmState_14 TMcommitted)
        (not (rmWorking_15 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_15 rm2) (rmWorking_14 rm2)))
            ) ;;;
        (not (rmPrepared_15 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_15 rm2) (rmPrepared_14 rm2)))
            ) ;;;
        (rmCommitted_15 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_15 rm2) (rmCommitted_14 rm2)))
            ) ;;;
        (not (rmAborted_15 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_15 rm2) (rmAborted_14 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_15 rm2) (sentPrepared_14 rm2)))
        (= tmState_15 tmState_14)
)))) ;;;

(assert (=> (= action_15 RMRcvAbortMsg)
    (exists ((rm RM)) (and
        (= tmState_14 TMaborted)
        (not (rmWorking_15 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmWorking_15 rm2) (rmWorking_14 rm2)))
            ) ;;;
        (not (rmPrepared_15 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmPrepared_15 rm2) (rmPrepared_14 rm2)))
            ) ;;;
        (not (rmCommitted_15 rm))
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmCommitted_15 rm2) (rmCommitted_14 rm2)))
            ) ;;;
        (rmAborted_15 rm)
        (forall ((rm2 RM))
            (or
              (= rm rm2)
              (= (rmAborted_15 rm2) (rmAborted_14 rm2)))
            ) ;;;
        (forall ((rm2 RM)) (= (sentPrepared_15 rm2) (sentPrepared_14 rm2)))
        (= tmState_15 tmState_14)
)))) ;;;
;; SAFETY
(assert (or
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_0 rm1) (rmCommitted_0 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_1 rm1) (rmCommitted_1 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_2 rm1) (rmCommitted_2 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_3 rm1) (rmCommitted_3 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_4 rm1) (rmCommitted_4 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_5 rm1) (rmCommitted_5 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_6 rm1) (rmCommitted_6 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_7 rm1) (rmCommitted_7 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_8 rm1) (rmCommitted_8 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_9 rm1) (rmCommitted_9 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_10 rm1) (rmCommitted_10 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_11 rm1) (rmCommitted_11 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_12 rm1) (rmCommitted_12 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_13 rm1) (rmCommitted_13 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_14 rm1) (rmCommitted_14 rm2 )))
    (exists ((rm1 RM) (rm2 RM))
        (and (rmAborted_15 rm1) (rmCommitted_15 rm2 )))
)) ;;;


(check-sat)
;;(get-model)
