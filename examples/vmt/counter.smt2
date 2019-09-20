; printed by MathSAT5 version 5.5.4 (bd863fede57e) (Feb 21 2019 15:08:33, gmp 6.1.0, gcc 4.8.5, 64-bit)

; state variables
(declare-fun .X () (_ BitVec 4))
(declare-fun .X$next () (_ BitVec 4))
(define-fun ..X () (_ BitVec 4) (! .X :next .X$next))

; input variables
(declare-fun .en () Bool)

; initial state
(define-fun .init () Bool (! 
; size 1
(and
	(= .X (_ bv1 4))
)
 :init true))

; transition relation main
(define-fun .T () Bool 
; size 1
(and
	(= .X$next (ite .en (ite (= .X (_ bv15 4)) (_ bv1 4) (bvadd (_ bv1 4) .X)) .X))
)
)

; transition relation
(define-fun .trans () Bool (! 
(and 
	.T
)
 :trans true))

; property expression
(define-fun .prop () Bool 
; size 1
(and
	(not (= .X (_ bv0 4)))
)
)

; property next expression
(define-fun .prop_next () Bool 
; size 1
(and
	(not (= .X$next (_ bv0 4)))
)
)

; property
(define-fun .property () Bool (! 
	.prop
 :invar-property 0))
