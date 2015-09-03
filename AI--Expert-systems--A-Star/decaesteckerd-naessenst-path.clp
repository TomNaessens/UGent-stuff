
;;
;;  Definition of the route information
;;

(deftemplate position
	(field name (type SYMBOL) (default NIL))
	(field x (type NUMBER))
	(field y (type NUMBER))
	(multifield neighbours (default NIL))
)


(deffacts network-positions
	(position (name A) (x 0) (y 0) (neighbours B C))
 	(position (name B) (x 0) (y 1) (neighbours A E D))
	(position (name C) (x 1) (y 0) (neighbours A I))
	(position (name D) (x 1) (y 1) (neighbours B F))
	(position (name E) (x 0) (y 2) (neighbours B F))
	(position (name F) (x 1) (y 2) (neighbours E D G))
	(position (name G) (x 2) (y 2) (neighbours F H))
	(position (name H) (x 2) (y 1) (neighbours G))
	(position (name I) (x 2) (y 0) (neighbours C))
)


;;
;;  Definition of the search tree
;;
;; Important: We added the fn value here to be able to select
;; the node with the minimal fn more easily
;;

(deftemplate node
	(field name (type SYMBOL) (default NIL))
	(field status (type SYMBOL))
	(field parent (type SYMBOL))
	(field x (type NUMBER) (default -1))
	(field y (type NUMBER) (default -1))
	(field depth (type NUMBER))
	(field fn (type NUMBER) (default 1000000000))
)

(deftemplate goal
	(field name (type SYMBOL) (default NIL))
	(field x (type NUMBER) (default -1))
	(field y (type NUMBER) (default -1))
)

(deftemplate start
	(field name (type SYMBOL) (default NIL))
	(field x (type NUMBER) (default -1))
	(field y (type NUMBER) (default -1))
)


;;
;;  Rule to determine the route connectivity
;;  The rule generates new search nodes in the search tree based on connectivity of active nodes
;;
;;  Important: we don't want to re-add closed nodes to the tree, so we add an extra condition to
;;  prohibit this
;;

(defrule Generate-neighbours
	(declare (salience 20))
	(node (name ?p) (status active) (depth ?g))
	(position (name ?p) (neighbours $? ?v $?))
	(not (node (name ?v) (status closed)))
=>
	(printout t "DEBUG: Generate neighbours of " ?p " " ?v crlf)
	(assert (node (name ?v) (status new) (parent ?p) (depth =(+ ?g 1)) ))
)

;;
;; Rule to put an active node on the closed list after children are generated
;;

(defrule Close-node
	(declare (salience 10))
	?N <- (node (status active))
=>
	(printout t "DEBUG: Close node " ?N crlf)
	(modify ?N (status closed))
)

;;
;; Gather the positional information in the search nodes 
;;

(defrule Gather-position-node
	(declare (salience 30))
	?N <- (node (name ?n) (x -1) (y -1))
	(position (name ?n) (x ?x) (y ?y))
=>
	(printout t "DEBUG: Gather position node " ?n crlf)
	(modify ?N (x ?x) (y ?y))
)

(defrule Gather-position-goal
	(declare (salience 10))
	?B <- (goal (name ?n) (x -1) (y -1))
	(position (name ?n) (x ?x) (y ?y))
=>
	(printout t "DEBUG: Gather position goal " ?n crlf)
	(modify ?B (x ?x) (y ?y))
)


(defrule Gather-position-start
	(declare (salience 10))
	?D <- (start (name ?n) (x -1) (y -1))
	(position (name ?n) (x ?x) (y ?y))
=>
	(printout t "DEBUG: Gather position start " ?n crlf)
	(modify ?D (x ?x) (y ?y))
)

;;
;; Rule to initialize the search
;;

(defrule init
	(initial-fact)
        (not (depart))
=>
	(printout t "Init" crlf)
	(printout t "The grid name of the start position? ")
	(bind ?n (read))
	(assert (start (name ?n) ))
	(printout t "The grid name of the end position? ")
	(bind ?n (read))
	(assert (goal (name ?n)))
)


;;
;; Rule to stop the search
;;

(defrule terminate-search
	(route $?r)
	?N <- (node (status open))
=>
	(modify ?N (status closed))
 	(halt)
)

;;
;; Rule to determine optimal path
;;

(defrule compose-route
	(declare (salience 1000))
	?C <- (route ?n $?q)
	(node (name ?n) (parent ?p&:(neq ?p nil)))
	(goal (name ?b))
	(test (neq ?p ?b))
=>
	(printout t "DEBUG: Compose route" crlf)
	(retract ?C)
	(assert (route ?p ?n $?q))
)

;;
;; Rule to printout the optimal path
;;
;; Important: For some reason, the NIL-parent of the root got appended
;; too, so we close put a placeholder here so the route gets printed
;;

(defrule print-route
	(declare (salience 1000))
	(route NIL ?d $?q ?b)
	(start (name ?d))
=>
	(printout t "The optimal path from " ?d " to " ?b " passes " $?q crlf)
	(halt)
)

;;;;;;;;;;;;;;;;;;;
;; Added methods ;;
;;;;;;;;;;;;;;;;;;;

;;
;; Create a root node in the search tree from the start node
;;

(defrule Set-start-node 
    (declare (salience 100))
	(start (name ?name) (x ?x) (y ?y))
	(not (node (name ?name)))
=> 
	(printout t "DEBUG: Set start node " ?name crlf)
	(assert (node (name ?name) (status open) (parent NIL) (depth 0)))
)

;;
;; Halt with failure when there is no open node and no route exists
;;

(defrule Halt-when-closed-empty
	(not (exists (node (status open))))
	(not (route $?))
=>
	(printout t "FAILURE" crlf)
	(halt)
)

;;
;; Select an open node and activate it
;; We select our node based on the A* algorithm:
;; * f(n) = h(n) + g(n)
;; * h(n) = estimated cost (manhattan distance, (|x1 - x2| + |y1 - y2|))
;; * g(n) = cost from the start node (depth in the tree)
;; We select the node whose f(n) is minimal
;;

;;
;; First we create a handy function to calculate the f(n) value
;;

(deffunction calculate-fn
	(?current-depth ?current-x ?current-y ?goal-x ?goal-y)
	(bind ?hn (+ (abs (- ?current-x ?goal-x)) (abs (- ?current-y ?goal-y))))
	(bind ?fn (+ ?hn ?current-depth))
	(return ?fn)
)

(defrule Update-fn
	(declare (salience 8))
	?N <- (node (status new) (name ?current-name) (x ?current-x) (y ?current-y) (depth ?current-depth))
	(goal (x ?goal-x) (y ?goal-y))
=>
	(bind ?fn (calculate-fn ?current-depth ?current-x ?current-y ?goal-x ?goal-y))
	(modify ?N (fn ?fn) (status open))
	(printout t "DEBUG: Setting " ?current-name " fn value to " ?fn crlf)
)
	

;;
;; Then we use our function to select the node with the minimal f(n)
;;

(defrule Select-active-node
	(declare (salience 5))
    ?active-node <- (node (name ?open-name) (status open) (x ?open-x) (y ?open-y) (fn ?open-fn))
    (not (node (fn ?fn&:(< ?fn ?open-fn)) (status open)))
=>
	(printout t "DEBUG: " ?open-name " has the lowest fn " ?open-fn crlf)
    (modify ?active-node (status active))
)

;;
;; Finishing statement: When we have an active node with the same name as our goal: SUCCESS
;;

(defrule Reach-goal
	(declare (salience 15))
	(node (name ?name) (status open))
	(goal (name ?name))
=>
	(printout t "SUCCESS: Reached " ?name crlf)
	(assert (route ?name))
)