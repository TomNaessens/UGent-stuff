; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the TRACE* book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
; only load for interactive sessions: 
#+acl2s-startup (include-book "trace-star" :uncertified-okp nil :dir :acl2s-modes :ttags ((:acl2s-interaction)) :load-compiled-file nil);v4.0 change

#+acl2s-startup (assign evalable-printing-abstractions nil)

;; ;arithmetic book
;; #+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading arithmetic-5/top book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
;; (include-book "arithmetic-5/top" :dir :system)

;basic thms/lemmas about lists
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)
;(include-book "coi/lists/basic" :dir :system)

;; #+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2's lexicographic-ordering-without-arithmetic book.~%This indicates that either your ACL2 installation is missing the standard books are they are not properly certified.") (value :invisible))
;; (include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :load-compiled-file :comp :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))


;Settings common to all ACL2s modes
(acl2s-common-settings)



(acl2::xdoc defunc)

; Non-events:
;(set-guard-checking :none)


; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;testentry: (addEntry '(("a" 1 3 5)("c" 2 5)) "a" 2)

;functie die een lege index maakt
(defun createIndex ()
  nil)

;functie die een woord met paginanummer toevoegt, als het woord al bestaat dan voeg nummer geordend toe
(defun addPage (page pageList)
  (cond ((endp pageList) (list page))
        ((< page (car pageList)) (cons page pageList))
        ((equal page (car pageList)) pageList)
        (t (cons (car pageList) (addPage page (cdr pageList))))
  )
)

;functie die een woord met paginanummer toevoegt, als het woord al bestaat dan voeg nummer geordend toe
(defun addEntry (index word page)
  (cond ((endp index) (list (list word page))) ; index is nil
        ((equal word (caar index)) (cons (cons word (addPage page (cdar index))) (cdr index))) ; word found, enter second level
        ((string< word (caar index)) (cons (list word page) index)) ; next is bigger but not equal
        (t (cons (car index) (addEntry (cdr index) word page)))
  )
)

;functie die de lijst van pag nummers teruggeeft voor een woord
(defun getPages (word index)
  (cond ((endp index) nil)
        ((equal word (caar index)) (cdar index))
        ((string< word (caar index)) nil)
        (t (getPages word (cdr index)))
  )
)

;functie die de lijst van woorden uit de index genereert
(defun getWords (index)
  (cond ((endp index) nil)
        (t (cons (caar index) (getWords (cdr index))))
  )
)