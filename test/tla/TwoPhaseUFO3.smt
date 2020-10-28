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
)) ;;;


(check-sat)
;;(get-model)
