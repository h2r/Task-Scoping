(define (problem MINECRAFTCONTRIVED-1)
    (:domain minecraft-contrived)


(:objects
	obsidian0 obsidian1 - obsidian-block
	steve - agent
	old-pointy - diamond-pickaxe
	dmd0 dmd1 dmd2 - diamond
	stick0 stick1 - stick
)


(:init
	(agent-alive steve)
	(= (x steve) 0)
	(= (y steve) 0)
	(= (z steve) 0)
	( = ( agent-num-iron steve ) 0 )
	( = ( agent-num-wool steve ) 0 )
	( = ( agent-num-diamond steve ) 0 )
	( = ( agent-num-stick steve ) 0 )
	( = ( agent-num-diamond-pickaxe steve ) 0 )
	( = ( agent-num-apple steve ) 0 )
	( = ( agent-num-potato steve ) 0 )
	( = ( agent-num-rabbit steve ) 0 )
	( = ( agent-num-diamond-axe steve ) 0 )
	( = ( agent-num-orchid-flower steve ) 0 )
	( = ( agent-num-daisy-flower steve ) 0 )
	( = ( agent-num-shears steve ) 0 )
	(= (x obsidian0) 0)
	(= (y obsidian0) 3)
	(= (z obsidian0) 1)
	(= (x obsidian1) 0)
	(= (y obsidian1) 3)
	(= (z obsidian1) 2)
	( = ( block-hits obsidian0 ) 0 )
	( = ( block-hits obsidian1 ) 0 )
	(= (x old-pointy) 0)
	(= (y old-pointy) 0)
	(= (z old-pointy) 0)
	( not ( present old-pointy ) )
	(= (x stick0) 1)
	(= (y stick0) 0)
	(= (z stick0) 0)
	( present stick0 )
	(= (x stick1) 1)
	(= (y stick1) 1)
	(= (z stick1) 0)
	( present stick1 )
	(= (x dmd0) 2)
	(= (y dmd0) 0)
	(= (z dmd0) 0)
	(present dmd0)
	(= (x dmd1) 2)
	(= (y dmd1) 1)
	(= (z dmd1) 0)
	(present dmd1)
	(= (x dmd2) 2)
	(= (y dmd2) 2)
	(= (z dmd2) 0)
	(present dmd2)
	(block-present obsidian0)
	(block-present obsidian1)
)


(:goal (and
            (not (block-present obsidian0 ))
        )
    )

    


)