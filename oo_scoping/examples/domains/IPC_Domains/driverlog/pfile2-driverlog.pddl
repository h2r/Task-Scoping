(define (problem DLOG-2-2-3)
	(:domain ipc_composite)
	(:objects
	driver1 - driver
	driver2 - driver
	truck1 - truck
	truck2 - truck
	package1 - obj
	package2 - obj
	package3 - obj
	s0 - location
	s1 - location
	s2 - location
	p0-1 - location
	p0-2 - location
	p1-0 - location
	p2-1 - location
	)
	(:init
	(located-at driver1 s0)
	(located-at driver2 s0)
	(located-at truck1 s0)
	(empty truck1)
	(located-at truck2 s1)
	(empty truck2)
	(located-at package1 s2)
	(located-at package2 s1)
	(located-at package3 s1)
	(path s0 p0-1)
	(path p0-1 s0)
	(path s1 p0-1)
	(path p0-1 s1)
	(= (time-to-walk s0 p0-1) 37)
	(= (time-to-walk p0-1 s0) 37)
	(= (time-to-walk s1 p0-1) 39)
	(= (time-to-walk p0-1 s1) 39)
	(path s0 p0-2)
	(path p0-2 s0)
	(path s2 p0-2)
	(path p0-2 s2)
	(= (time-to-walk s0 p0-2) 68)
	(= (time-to-walk p0-2 s0) 68)
	(= (time-to-walk s2 p0-2) 7)
	(= (time-to-walk p0-2 s2) 7)
	(path s2 p2-1)
	(path p2-1 s2)
	(path s1 p2-1)
	(path p2-1 s1)
	(= (time-to-walk s2 p2-1) 30)
	(= (time-to-walk p2-1 s2) 30)
	(= (time-to-walk s1 p2-1) 19)
	(= (time-to-walk p2-1 s1) 19)
	(link s0 s2)
	(link s2 s0)
	(= (time-to-drive s0 s2) 52)
	(= (time-to-drive s2 s0) 52)
	(link s1 s0)
	(link s0 s1)
	(= (time-to-drive s1 s0) 63)
	(= (time-to-drive s0 s1) 63)
	(link s1 s2)
	(link s2 s1)
	(= (time-to-drive s1 s2) 86)
	(= (time-to-drive s2 s1) 86)
	(= (driven) 0)
	(= (walked) 0)
)
	(:goal (and
			(located-at driver1 s1)
			(located-at driver2 s1)
			(located-at truck1 s2)
			(located-at truck2 s0)
			(located-at package1 s0)
			(located-at package2 s2)
			(located-at package3 s0)
		   )
	)

; (:metric minimize (+ (+ (* 2  (total-time)) (* 4  (driven))) (* 1  (walked))))

)
