(define (problem MULTIMONKEY-02)
(:domain multi_monkeys_playroom)
(:objects
	; jack - monkey
	jack - monkey
    bell1 - bell
    ; ball1 - ball
    ball1 ball2 - ball
    eye1 - eye
    hand1 - hand
    marker1 - marker
    ; rb1 - redbutton
    rb1 rb2 - redbutton
    gb1 gb2 - greenbutton
    ; ls1 - lightswitch
    ls1 ls2 ls3 - lightswitch
)
(:init
    (= (eye-x eye1) 0)
    (= (eye-y eye1) 0)

    (= (hand-x hand1) 0)
    (= (hand-y hand1) 0)

    (= (marker-x marker1) 0)
    (= (marker-y marker1) 0)

    (= (lightswitch-x ls1) 2)
    (= (lightswitch-y ls1) 2)
    (light-on ls1)
    (= (lightswitch-x ls2) 2)
    (= (lightswitch-y ls2) 3)
    (light-on ls2)
    (= (lightswitch-x ls3) 2)
    (= (lightswitch-y ls3) 4)
    (light-on ls3)

    (= (rbutton-x rb1) 3)
    (= (rbutton-y rb1) 3)
    (= (rbutton-x rb2) 5)
    (= (rbutton-y rb2) 3)
    (= (gbutton-x gb1) 3)
    (= (gbutton-y gb1) 4)
    (= (gbutton-x gb2) 4)
    (= (gbutton-y gb2) 3)
    (not (rbutton-on rb1))
    (not (rbutton-on rb2))
    (gbutton-on gb1)
    ; (not (gbutton-on gb2))
    (gbutton-on gb2)
    (connected-buttons rb1 gb1)
    ; (connected-buttons rb1 gb2)
    (connected-buttons rb2 gb2)
    (not (connected-buttons rb1 gb2))
    (not (connected-buttons rb2 gb1))

    (= (ball-x ball1) 5)
    (= (ball-y ball1) 5)
    (= (ball-x ball2) 5)
    (= (ball-y ball2) 6)

    (= (bell-x bell1) 10)
    (= (bell-y bell1) 10)
 
    (not (monkey-screaming jack))
    (monkey-watching-bell jack bell1)

;    (monkey-screaming caesar)
;    (monkey-watching-bell caesar bell1)

)

(:goal (monkey-screaming jack))

)