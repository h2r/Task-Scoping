(define (problem MINECRAFTCONTRIVED-3)
    (:domain minecraft-bedmaking)


(:objects
	steve - agent
	old-pointy - diamond-axe
	of0 of1 of2 - orchid-flower
	wb0 wb1 wb2 wb3 wb4 wb5 wb6 wb7 wb8 wb9 wb10 wb11 wb12 wb13 wb14 wb15 wb16 wb17 wb18 wb19 wb20 wb21 wb22 wb23 wb24 wb25 wb26 wb27 wb28 wb29 wb30 - wooden-block
	woolb1 woolb2 woolb3 - wool-block
	bed1 - bed
	dmd0 dmd1 dmd2 dmd3 dmd4 - diamond
	stick0 stick1 stick2 stick3 stick4 - stick
	rt0 rt1 rt2 rt3 rt4 rt5 rt6 rt7 rt8 rt9 rt10 rt11 rt12 rt13 rt14 rt15 rt16 rt17 rt18 rt19 - red-tulip
	df0 df1 df2 df3 df4 df5 df6 df7 df8 df9 df10 df11 - daisy-flower
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
	( = ( item-hits rt0 ) 0 )
	( = ( item-hits rt1 ) 0 )
	( = ( item-hits rt2 ) 0 )
	( = ( item-hits rt3 ) 0 )
	( = ( item-hits rt4 ) 0 )
	( = ( item-hits rt5 ) 0 )
	( = ( item-hits rt6 ) 0 )
	( = ( item-hits rt7 ) 0 )
	( = ( item-hits rt8 ) 0 )
	( = ( item-hits rt9 ) 0 )
	( = ( item-hits rt10 ) 0 )
	( = ( item-hits rt11 ) 0 )
	( = ( item-hits rt12 ) 0 )
	( = ( item-hits rt13 ) 0 )
	( = ( item-hits rt14 ) 0 )
	( = ( item-hits rt15 ) 0 )
	( = ( item-hits rt16 ) 0 )
	( = ( item-hits rt17 ) 0 )
	( = ( item-hits rt18 ) 0 )
	( = ( item-hits rt19 ) 0 )
	(= (agent-num-red-tulip steve) 0)
	( = ( item-hits df0 ) 0 )
	( = ( item-hits df1 ) 0 )
	( = ( item-hits df2 ) 0 )
	( = ( item-hits df3 ) 0 )
	( = ( item-hits df4 ) 0 )
	( = ( item-hits df5 ) 0 )
	( = ( item-hits df6 ) 0 )
	( = ( item-hits df7 ) 0 )
	( = ( item-hits df8 ) 0 )
	( = ( item-hits df9 ) 0 )
	( = ( item-hits df10 ) 0 )
	( = ( item-hits df11 ) 0 )
	(= (agent-num-daisy-flower steve) 0)
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
	(= (x stick0) 0)
	(= (y stick0) 2)
	(= (z stick0) 0)
	( present stick0 )
	(= (x stick1) 0)
	(= (y stick1) 3)
	(= (z stick1) 0)
	( present stick1 )
	(= (x stick2) 0)
	(= (y stick2) 4)
	(= (z stick2) 0)
	( present stick2 )
	(= (x stick3) 0)
	(= (y stick3) 5)
	(= (z stick3) 0)
	( present stick3 )
	(= (x stick4) 0)
	(= (y stick4) 6)
	(= (z stick4) 0)
	( present stick4 )
	(= (x dmd0) 1)
	(= (y dmd0) 2)
	(= (z dmd0) 0)
	(present dmd0)
	(= (x dmd1) 1)
	(= (y dmd1) 3)
	(= (z dmd1) 0)
	(present dmd1)
	(= (x dmd2) 1)
	(= (y dmd2) 4)
	(= (z dmd2) 0)
	(present dmd2)
	(= (x dmd3) 1)
	(= (y dmd3) 5)
	(= (z dmd3) 0)
	(present dmd3)
	(= (x dmd4) 1)
	(= (y dmd4) 6)
	(= (z dmd4) 0)
	(present dmd4)
	(= (x rt0) 2)
	(= (y rt0) 6)
	(= (z rt0) 0)
	(present rt0)
	(= (x rt1) 3)
	(= (y rt1) 6)
	(= (z rt1) 0)
	(present rt1)
	(= (x rt2) 4)
	(= (y rt2) 6)
	(= (z rt2) 0)
	(present rt2)
	(= (x rt3) 5)
	(= (y rt3) 6)
	(= (z rt3) 0)
	(present rt3)
	(= (x rt4) 6)
	(= (y rt4) 6)
	(= (z rt4) 0)
	(present rt4)
	(= (x rt5) 7)
	(= (y rt5) 6)
	(= (z rt5) 0)
	(present rt5)
	(= (x rt6) 8)
	(= (y rt6) 6)
	(= (z rt6) 0)
	(present rt6)
	(= (x rt7) 8)
	(= (y rt7) 5)
	(= (z rt7) 0)
	(present rt7)
	(= (x rt8) 8)
	(= (y rt8) 4)
	(= (z rt8) 0)
	(present rt8)
	(= (x rt9) 8)
	(= (y rt9) 3)
	(= (z rt9) 0)
	(present rt9)
	(= (x rt10) 8)
	(= (y rt10) 2)
	(= (z rt10) 0)
	(present rt10)
	(= (x rt11) 7)
	(= (y rt11) 2)
	(= (z rt11) 0)
	(present rt11)
	(= (x rt12) 6)
	(= (y rt12) 2)
	(= (z rt12) 0)
	(present rt12)
	(= (x rt13) 5)
	(= (y rt13) 2)
	(= (z rt13) 0)
	(present rt13)
	(= (x rt14) 4)
	(= (y rt14) 2)
	(= (z rt14) 0)
	(present rt14)
	(= (x rt15) 3)
	(= (y rt15) 2)
	(= (z rt15) 0)
	(present rt15)
	(= (x rt16) 2)
	(= (y rt16) 2)
	(= (z rt16) 0)
	(present rt16)
	(= (x rt17) 2)
	(= (y rt17) 3)
	(= (z rt17) 0)
	(present rt17)
	(= (x rt18) 2)
	(= (y rt18) 4)
	(= (z rt18) 0)
	(present rt18)
	(= (x rt19) 2)
	(= (y rt19) 5)
	(= (z rt19) 0)
	(present rt19)
	(= (x df0) 3)
	(= (y df0) 5)
	(= (z df0) 0)
	( present df0 )
	(= (x df1) 4)
	(= (y df1) 5)
	(= (z df1) 0)
	( present df1 )
	(= (x df2) 5)
	(= (y df2) 5)
	(= (z df2) 0)
	( present df2 )
	(= (x df3) 6)
	(= (y df3) 5)
	(= (z df3) 0)
	( present df3 )
	(= (x df4) 7)
	(= (y df4) 5)
	(= (z df4) 0)
	( present df4 )
	(= (x df5) 7)
	(= (y df5) 4)
	(= (z df5) 0)
	( present df5 )
	(= (x df6) 7)
	(= (y df6) 3)
	(= (z df6) 0)
	( present df6 )
	(= (x df7) 6)
	(= (y df7) 3)
	(= (z df7) 0)
	( present df7 )
	(= (x df8) 5)
	(= (y df8) 3)
	(= (z df8) 0)
	( present df8 )
	(= (x df9) 4)
	(= (y df9) 3)
	(= (z df9) 0)
	( present df9 )
	(= (x df10) 3)
	(= (y df10) 3)
	(= (z df10) 0)
	( present df10 )
	(= (x df11) 3)
	(= (y df11) 4)
	(= (z df11) 0)
	( present df11 )
)

; For this problem, scoping somehow has one less pvar from one
; iter to the next...
(:goal (and (>= (agent-num-diamond-axe steve) 3))
)


)