; Scaling-up the domain to see how much slower FD's search gets

(define (problem MULTIMONKEY-01)
(:domain multi_monkeys_playroom_strips)
(:objects
    ls1 ls2 ls3 - lightswitch
    x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 - x-loc
    y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 - y-loc
    red blue green white black yellow - color
)
(:init
    ; establishing adjacency
    (adjacent-x x1 x2)
    (adjacent-x x2 x1)
    (adjacent-x x2 x3)
    (adjacent-x x3 x2)
    (adjacent-x x3 x4)
    (adjacent-x x4 x3)
    (adjacent-x x4 x5)
    (adjacent-x x5 x4)
    (adjacent-x x5 x6)
    (adjacent-x x6 x5)
    (adjacent-x x6 x7)
    (adjacent-x x7 x6)
    (adjacent-x x7 x8)
    (adjacent-x x8 x7)
    (adjacent-x x8 x9)
    (adjacent-x x9 x8)
    (adjacent-x x9 x10)
    (adjacent-x x10 x9)
    (adjacent-x x10 x11)
    (adjacent-x x11 x10)
    (adjacent-x x11 x12)
    (adjacent-x x12 x11)
    (adjacent-x x12 x13)
    (adjacent-x x13 x12)
    (adjacent-x x13 x14)
    (adjacent-x x14 x13)
    (adjacent-x x14 x15)
    (adjacent-x x15 x14)
    (adjacent-x x15 x16)
    (adjacent-x x16 x15)
    (adjacent-x x16 x17)
    (adjacent-x x17 x16)
    (adjacent-x x17 x18)
    (adjacent-x x18 x17)
    (adjacent-x x18 x19)
    (adjacent-x x19 x18)
    (adjacent-x x19 x20)
    (adjacent-x x20 x19)
    (adjacent-y y1 y2)
    (adjacent-y y2 y1)
    (adjacent-y y2 y3)
    (adjacent-y y3 y2)
    (adjacent-y y3 y4)
    (adjacent-y y4 y3)
    (adjacent-y y4 y5)
    (adjacent-y y5 y4)
    (adjacent-y y5 y6)
    (adjacent-y y6 y5)
    (adjacent-y y6 y7)
    (adjacent-y y7 y6)
    (adjacent-y y7 y8)
    (adjacent-y y8 y7)
    (adjacent-y y8 y9)
    (adjacent-y y9 y8)
    (adjacent-y y9 y10)
    (adjacent-y y10 y9)
    (adjacent-y y10 y11)
    (adjacent-y y11 y10)
    (adjacent-y y11 y12)
    (adjacent-y y12 y11)
    (adjacent-y y12 y13)
    (adjacent-y y13 y12)
    (adjacent-y y13 y14)
    (adjacent-y y14 y13)
    (adjacent-y y14 y15)
    (adjacent-y y15 y14)
    (adjacent-y y15 y16)
    (adjacent-y y16 y15)
    (adjacent-y y16 y17)
    (adjacent-y y17 y16)
    (adjacent-y y17 y18)
    (adjacent-y y18 y17)
    (adjacent-y y18 y19)
    (adjacent-y y19 y18)
    (adjacent-y y19 y20)
    (adjacent-y y20 y19)
    
    ; eye initial locations    
    (eye-x x1)
    (eye-y y10)

    ; hand initial locations
    (hand-x x1)
    (hand-y y10)

    ; lightswitch initial locations
    (lightswitch-x ls1 x20)
    (lightswitch-y ls1 y10)
    (light-on ls1)

    (lightswitch-x ls2 x19)
    (lightswitch-y ls2 y10)
    (not (light-on ls2))

    (lightswitch-x ls3 x18)
    (lightswitch-y ls3 y10)
    (not (light-on ls3))

    (lightswitch-color ls1 red)
    (lightswitch-color ls2 blue)
    (lightswitch-color ls3 green)

)

(:goal (and (not (light-on ls1))
            (not (light-on ls2))
            (not (light-on ls3))
            (lightswitch-color ls1 red)
        )
)

)