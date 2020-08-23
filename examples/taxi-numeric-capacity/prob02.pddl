(define (problem TAXINUMERIC-2)
(:domain multipasstaxi)
(:objects
	curly smoov - passenger

	; curly smoov littman isbell tellex konidaris kaelbling perez levine abbeel - passenger
	; curly - passenger
    t0 - taxi
)
(:init
    (= (taxi-x t0) 0)
    (= (taxi-y t0) 0)
    (not (in-taxi curly t0))
    (not (in-taxi smoov t0))
    ; (not (in-taxi littman t0))
    ; (not (in-taxi isbell t0))
    ; (not (in-taxi tellex t0))
    ; (not (in-taxi konidaris t0))
    ; (not (in-taxi kaelbling t0))
    ; (not (in-taxi perez t0))
    ; (not (in-taxi levine t0))
    ; (not (in-taxi abbeel t0))
    (= (pass-x curly) 15)
    (= (pass-y curly) 23)
    (= (pass-x smoov) 2)
    (= (pass-y smoov) 1)
    ; (= (pass-x littman) 1)
    ; (= (pass-y littman) 2)
    ; (= (pass-x isbell) 1)
    ; (= (pass-y isbell) 1)
    ; (= (pass-x tellex) 2)
    ; (= (pass-y tellex) 2)
    ; (= (pass-x konidaris) 0)
    ; (= (pass-y konidaris) 1)
    ; (= (pass-x kaelbling) 1)
    ; (= (pass-y kaelbling) 0)
    ; (= (pass-x perez) 0)
    ; (= (pass-y perez) 2)
    ; (= (pass-x levine) 2)
    ; (= (pass-y levine) 0)
    ; (= (pass-x abbeel) 0)
    ; (= (pass-y abbeel) 0)
    (= (passenger-count t0) 0)
)
(:goal (and
    (= (pass-y curly) 1050)
	(= (pass-x curly) 830)
    (not (in-taxi curly t0))
	
    )
    )
;(:metric  minimize (total-fuel-used) )

)