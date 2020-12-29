(define (problem MINECRAFTCONTRIVED-3)
    (:domain minecraft-bedmaking)


(:objects
	steve - agent
	old-pointy - diamond-axe
	of0 of1 of2 - orchid-flower
	wb0 wb1 wb2 wb3 wb4 wb5 wb6 wb7 wb8 wb9 wb10 wb11 wb12 wb13 wb14 wb15 wb16 wb17 wb18 wb19 wb20 wb21 wb22 wb23 wb24 wb25 wb26 wb27 wb28 wb29 wb30 - wooden-block
	woolb1 woolb2 woolb3 - wool-block
	bed1 - bed
)


(:init
	(agent-alive steve)
	(= (x wb0) 7)
	(= (y wb0) 7)
	(= (z wb0) 0)
	(block-present wb0)
	(= (x wb1) 6)
	(= (y wb1) 7)
	(= (z wb1) 0)
	(block-present wb1)
	(= (x wb2) 8)
	(= (y wb2) 7)
	(= (z wb2) 0)
	(block-present wb2)
	(= (x wb3) 5)
	(= (y wb3) 8)
	(= (z wb3) 0)
	(block-present wb3)
	(= (x wb4) 9)
	(= (y wb4) 8)
	(= (z wb4) 0)
	(block-present wb4)
	(= (x wb5) 5)
	(= (y wb5) 9)
	(= (z wb5) 0)
	(block-present wb5)
	(= (x wb6) 9)
	(= (y wb6) 9)
	(= (z wb6) 0)
	(block-present wb6)
	(= (x wb7) 6)
	(= (y wb7) 10)
	(= (z wb7) 0)
	(block-present wb7)
	(= (x wb8) 7)
	(= (y wb8) 11)
	(= (z wb8) 0)
	(block-present wb8)
	(= (x wb9) 8)
	(= (y wb9) 10)
	(= (z wb9) 0)
	(block-present wb9)
	(= (x wb10) 6)
	(= (y wb10) 7)
	(= (z wb10) 1)
	(block-present wb10)
	(= (x wb11) 8)
	(= (y wb11) 7)
	(= (z wb11) 1)
	(block-present wb11)
	(= (x wb12) 5)
	(= (y wb12) 8)
	(= (z wb12) 1)
	(block-present wb12)
	(= (x wb13) 9)
	(= (y wb13) 8)
	(= (z wb13) 1)
	(block-present wb13)
	(= (x wb14) 5)
	(= (y wb14) 9)
	(= (z wb14) 1)
	(block-present wb14)
	(= (x wb15) 9)
	(= (y wb15) 9)
	(= (z wb15) 1)
	(block-present wb15)
	(= (x wb16) 6)
	(= (y wb16) 10)
	(= (z wb16) 1)
	(block-present wb16)
	(= (x wb17) 7)
	(= (y wb17) 11)
	(= (z wb17) 1)
	(block-present wb17)
	(= (x wb18) 8)
	(= (y wb18) 10)
	(= (z wb18) 1)
	(block-present wb18)
	(= (x wb19) 6)
	(= (y wb19) 7)
	(= (z wb19) 2)
	(block-present wb19)
	(= (x wb20) 7)
	(= (y wb20) 7)
	(= (z wb20) 2)
	(block-present wb20)
	(= (x wb21) 8)
	(= (y wb21) 7)
	(= (z wb21) 2)
	(block-present wb21)
	(= (x wb22) 6)
	(= (y wb22) 8)
	(= (z wb22) 2)
	(block-present wb22)
	(= (x wb23) 8)
	(= (y wb23) 8)
	(= (z wb23) 2)
	(block-present wb23)
	(= (x wb24) 6)
	(= (y wb24) 9)
	(= (z wb24) 2)
	(block-present wb24)
	(= (x wb25) 8)
	(= (y wb25) 9)
	(= (z wb25) 2)
	(block-present wb25)
	(= (x wb26) 6)
	(= (y wb26) 10)
	(= (z wb26) 2)
	(block-present wb26)
	(= (x wb27) 8)
	(= (y wb27) 10)
	(= (z wb27) 2)
	(block-present wb27)
	(= (x wb28) 6)
	(= (y wb28) 10)
	(= (z wb28) 2)
	(block-present wb28)
	(= (x wb29) 7)
	(= (y wb29) 10)
	(= (z wb29) 2)
	(block-present wb29)
	(= (x wb30) 8)
	(= (y wb30) 10)
	(= (z wb30) 2)
	(block-present wb30)
	(= (x steve) 7)
	(= (y steve) 1)
	(= (z steve) 0)
	( = ( agent-num-diamond steve ) 0 )
	( = ( agent-num-stick steve ) 0 )
	( = ( agent-num-diamond-axe steve ) 1 )
	( = ( agent-num-white-dye steve ) 0 )
	( = ( agent-num-blue-dye steve ) 0 )
	( = ( agent-num-red-dye steve ) 0 )
	( = ( agent-num-wool-block steve ) 3 )
	( = ( block-hits wb0 ) 0 )
	( = ( block-hits wb1 ) 0 )
	( = ( block-hits wb2 ) 0 )
	( = ( block-hits wb3 ) 0 )
	( = ( block-hits wb4 ) 0 )
	( = ( block-hits wb5 ) 0 )
	( = ( block-hits wb6 ) 0 )
	( = ( block-hits wb7 ) 0 )
	( = ( block-hits wb8 ) 0 )
	( = ( block-hits wb9 ) 0 )
	( = ( block-hits wb10 ) 0 )
	( = ( block-hits wb11 ) 0 )
	( = ( block-hits wb12 ) 0 )
	( = ( block-hits wb13 ) 0 )
	( = ( block-hits wb14 ) 0 )
	( = ( block-hits wb15 ) 0 )
	( = ( block-hits wb16 ) 0 )
	( = ( block-hits wb17 ) 0 )
	( = ( block-hits wb18 ) 0 )
	( = ( block-hits wb19 ) 0 )
	( = ( block-hits wb20 ) 0 )
	( = ( block-hits wb21 ) 0 )
	( = ( block-hits wb22 ) 0 )
	( = ( block-hits wb23 ) 0 )
	( = ( block-hits wb24 ) 0 )
	( = ( block-hits wb25 ) 0 )
	( = ( block-hits wb26 ) 0 )
	( = ( block-hits wb27 ) 0 )
	( = ( block-hits wb28 ) 0 )
	( = ( block-hits wb29 ) 0 )
	( = ( block-hits wb30 ) 0 )
	(= (agent-num-wooden-block steve) 0)
	(= (agent-num-wooden-planks steve) 0)
	( = ( block-hits woolb1 ) 0 )
	(not (block-present woolb1))
	( = ( wool-color woolb1 ) 0 )
	( = ( block-hits woolb2 ) 0 )
	(not (block-present woolb2))
	( = ( wool-color woolb2 ) 1 )
	( = ( block-hits woolb3 ) 0 )
	(not (block-present woolb3))
	( = ( wool-color woolb3 ) 1 )
	(= (agent-num-wool-block steve) 3)
	(= (x bed1) 0)
	(= (y bed1) 0)
	(= (z bed1) 0)
	( = ( block-hits bed1 ) 0 )
	( = ( bed-color bed1 ) 0 )
	(not (block-present bed1))
	(= (agent-num-bed steve) 0)
	( = ( item-hits of0 ) 0 )
	( = ( item-hits of1 ) 0 )
	( = ( item-hits of2 ) 0 )
	(= (agent-num-orchid-flower steve) 0)
	(= (x old-pointy) 0)
	(= (y old-pointy) 0)
	(= (z old-pointy) 0)
	( not ( present old-pointy ) )
	(= (x of0) 4)
	(= (y of0) 4)
	(= (z of0) 0)
	( present of0 )
	(= (x of1) 5)
	(= (y of1) 4)
	(= (z of1) 0)
	( present of1 )
	(= (x of2) 6)
	(= (y of2) 4)
	(= (z of2) 0)
	( present of2 )
)


(:goal (and 
                    (= (x bed1) 7)
                    (= (y bed1) 9)
                    (= (z bed1) 0)
                    (= (bed-color bed1) 1)
            (not (block-present wb0))
                (block-present wb1)
                (block-present wb2)
                (block-present wb3)
                (block-present wb4)
                (block-present wb5)
                (block-present wb6)
                (block-present wb7)
                (block-present wb8)
                (block-present wb9)
                (block-present wb10)
                (block-present wb11)
                (block-present wb12)
                (block-present wb13)
                (block-present wb14)
                (block-present wb15)
                (block-present wb16)
                (block-present wb17)
                (block-present wb18)
                (block-present wb19)
                (block-present wb20)
                (block-present wb21)
                (block-present wb22)
                (block-present wb23)
                (block-present wb24)
                (block-present wb25)
                (block-present wb26)
                (block-present wb27)
                (block-present wb28)
                (block-present wb29)
                (block-present wb30))
)


)