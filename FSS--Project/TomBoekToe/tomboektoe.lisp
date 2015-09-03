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
;========== Helper functions ==========

;sorted check for lists
(defun is-ordered (lst)
  (or (endp lst)
      (endp (cdr lst))
      (and (<= (car lst) (car (cdr lst)))
           (is-ordered (cdr lst)))))

;sorted check for lists of strings
(defun is-ordered-string (lst)
  (or (endp lst)
      (endp (cdr lst))
      (and (alphorder (car lst) (car (cdr lst)))
           (is-ordered-string (cdr lst)))))

;======================================

;definie van de datastructuur: een geordende alist van geordende integer-lists
(defun indexp (index)
  (cond ((not (alistp index)) nil)
        ((endp index) t)
        ((not (stringp (caar index))) nil)
        ((not (is-ordered-string (strip-cars index))) nil)
        ((not (Nat-listp (cdar index))) nil)
        ((not (is-ordered (cdar index))) nil)
        (t (indexp (cdr index)))))

;functie die een lege index maakt
(defun createIndex ()
  nil
)

;verificatie: createIndex geeft een correcte index terug
(defthm createIndex-correctness
  (indexp (createIndex)))

;functie die de lijst van woorden uit de index genereert
(defun getWords (index)
  (strip-cars index))

;verificatie: getWords geeft een geordende lijst terug
(defthm getWords-ordered
  (implies (indexp x)
           (is-ordered-string (getWords x))))

;verificatie: alle woorden uit de index zijn omvat in de lijst
;deze verificatie is eigenlijk overbodig aangezien de getWords
;functie enkel bestaat uit een reeds door ACL2 geverifieerde
;functie
(defthm getWords-gets-words
  (implies (and (indexp x))
           (eq (getWords x) (strip-cars x))))
           
;functie die de lijst van pag nummers teruggeeft voor een woord
(defun getPages (word index)
  (cond ((endp index) nil)
        ((equal word (caar index)) (cdar index))
        ((alphorder word (caar index)) nil)
        (t (getPages word (cdr index)))))

;verificatie: getPages geeft een geordende lijst terug
(defthm getPages-ordered
  (implies (and (stringp word)
                (indexp x))
           (is-ordered (getPages word x))))

;functie paginanummer geordend toevoegt aan een lijst van paginanummers
(defun addPage (page pageList)
  (cond ((endp pageList) (list page))
        ((< page (car pageList)) (cons page pageList))
        ((equal page (car pageList)) pageList)
        (t (cons (car pageList) (addPage page (cdr pageList))))))

;verificatie: addPage behoudt de orde
(defthm addPage-ordered
  (implies (is-ordered x)
           (is-ordered (addPage a x))))

;verificatie: nieuw element is effectief opgenomen
(defthm addPage-adds
  (implies (not (member a x))
           (member a (addPage a x))))

;functie om een element toe te voegen aan de index
(defun addEntry (word page index)
  (cond ((endp index) (put-assoc word (list page) index))
        ((equal word (caar index)) (cons (cons word (addPage page (cdar index))) (cdr index)))
        ((alphorder word (caar index)) (cons (list word page) index))
        (t (cons (car index) (addEntry word page (cdr index))))))

;verificatie als element nog niet in index, dan wel na addEntry
(defthm addEntry-adds
  (implies (and (stringp a)
                (natp n)
                (indexp x)
                (not (member a (getWords x))))
           (member a (getWords (addEntry a n x)))))

;verificatie: als element wel in index, maar paginanummer niet in de paginanummers, achteraf wel en lengte pages list +1
(defthm addEntry-adds-non-existing-pages-to-existing-words
  (implies (and (stringp a)
                (natp n)
                (indexp x)
                (member a (getWords x))
                (not (member n (getPages a x))))
           (eq (+ 1 (len (getPages a x))) (len (getPages a (addEntry a n x))))))

;verificatie: als element wel in index en paginanummer wel in de paginanummers, dan blijft deze lijst gelijk
(defthm addEntry-doesnt-add-existing-pages-to-existing-words
  (implies (and (stringp a)
                (natp n)
                (indexp x)
                (member a (getWords x))
                (member n (getPages a x)))
           (equal (getPages a x) (getPages a (addEntry a n x)))))

;verificatie: resultaat addEntry is een correcte index (intern alles gesorteerd)
(defthm addEntry-still-index
  (implies (and (stringp a)
                (natp n)
                (indexp x))
           (indexp (addEntry a n x)))
  :hints                      ;hier geven we de hint mee dat ACL2 niet dient te generaliseren, 
   (("Goal"                   ;aangezien dit problemen opleverde bij het bewijzen van dit theorema
     :do-not '(generalize))))


;verificatie: getPages lijst overeenkomstig met die in de index
;dit theorema staat nogal "out of place" aangezien andere theorema's
;niet geverifieerd werden.
(defthm getPages-gets-pages
  (implies (and (stringp word)
                (indexp x))
           (equal (getPages word x) (cdr (assoc-equal word x))))
  :hints                    ;hier geven we de hint mee dat ACL2 niet dient te generaliseren, 
   (("Goal"                 ;aangezien dit problemen opleverde bij het bewijzen van dit theorema
     :do-not '(generalize))))