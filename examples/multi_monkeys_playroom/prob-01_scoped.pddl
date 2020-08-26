(define (problem MULTIMONKEY-01)
(:domain multi_monkeys_playroom)
(:objects
	george - monkey
    bell1 - bell
    ball1 - ball
    eye1 - eye
    hand1 - hand
    marker1 - marker
    - redbutton
    - greenbutton
    - lightswitch
)
(:init
    (= (eye-x eye1) 0)
    (= (eye-y eye1) 0)

    (= (hand-x hand1) 0)
    (= (hand-y hand1) 0)

    (= (marker-x marker1) 0)
    (= (marker-y marker1) 0)

;    (= (lightswitch-x ls1) 2)
;    (= (lightswitch-y ls1) 2)
;    (not (light-on ls1))

;    (= (rbutton-x rb1) 3)
;    (= (rbutton-y rb1) 3)
;    (= (gbutton-x gb1) 3)
;    (= (gbutton-y gb1) 4)
;    (not (rbutton-on rb1))
;    (gbutton-on gb1)
;    (connected-buttons rb1 gb1)

    (= (ball-x ball1) 5)
    (= (ball-y ball1) 5)
    (monkey-watching-bell george bell1)

    (= (bell-x bell1) 5)
    (= (bell-y bell1) 6)

    (not (monkey-screaming george))
)

;; (:goal (gbutton-on gb1))

(:goal (monkey-screaming george))

)