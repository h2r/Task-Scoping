(define (problem INFTAXINUMERIC-1)
(:domain infinite_multipasstaxi)
(:objects
	; curly smoov - passenger
	curly smoov littman isbell tellex konidaris kaelbling perez levine abbeel - passenger
	; curly - passenger
    t0 - taxi
)
(:init
    (= (taxi-x t0) 0)
    (= (taxi-y t0) 0)
    (not (passenger-in-taxi curly t0))
    (not (passenger-in-taxi smoov t0))
    (not (passenger-in-taxi littman t0))
    (not (passenger-in-taxi isbell t0))
    (not (passenger-in-taxi tellex t0))
    (not (passenger-in-taxi konidaris t0))
    (not (passenger-in-taxi kaelbling t0))
    (not (passenger-in-taxi perez t0))
    (not (passenger-in-taxi levine t0))
    (not (passenger-in-taxi abbeel t0))
    (= (passenger-x curly) 15)
    (= (passenger-y curly) 23)
    (= (passenger-x smoov) 2)
    (= (passenger-y smoov) 1)
    (= (passenger-x littman) 1)
    (= (passenger-y littman) 2)
    (= (passenger-x isbell) 1)
    (= (passenger-y isbell) 1)
    (= (passenger-x tellex) 2)
    (= (passenger-y tellex) 2)
    (= (passenger-x konidaris) 0)
    (= (passenger-y konidaris) 1)
    (= (passenger-x kaelbling) 1)
    (= (passenger-y kaelbling) 0)
    (= (passenger-x perez) 0)
    (= (passenger-y perez) 2)
    (= (passenger-x levine) 2)
    (= (passenger-y levine) 0)
    (= (passenger-x abbeel) 0)
    (= (passenger-y abbeel) 0)
)
(:goal (and
    (= (passenger-y curly) 10)
	(= (passenger-x curly) 8)
    (not (passenger-in-taxi curly t0))
	
    )
    )
;(:metric  minimize (total-fuel-used) )

)