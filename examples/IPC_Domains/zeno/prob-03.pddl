(define (problem ZTRAVEL-1-4)
(:domain zenotravel)
(:objects
	plane1 plane2 - aircraft
	person1 person2 person3 - person
	city0 city2 - city
	)
(:init
	(located plane1 city0)
	(= (capacity plane1) 6000)
	(= (fuel plane1) 4000)
	(= (slow-burn plane1) 4)
	(= (fast-burn plane1) 15)
	(= (onboard plane1) 0)
	(= (zoom-limit plane1) 8)
    
    (located plane2 city0)
	(= (capacity plane2) 6000)
	(= (fuel plane2) 4000)
	(= (slow-burn plane2) 4)
	(= (fast-burn plane2) 15)
	(= (onboard plane2) 0)
	(= (zoom-limit plane2) 8)

	(located person1 city0)
	(located person2 city0)
	(located person3 city0)
	(= (distance city0 city0) 0)
	(= (distance city0 city2) 775)
	(= (distance city2 city0) 775)
	(= (distance city2 city2) 0)
	(= (total-fuel-used) 0)

)
(:goal (and	
	(located person1 city2)
	(located person2 city2)
	(located person3 city2)
	))
)
