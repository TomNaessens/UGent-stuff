------------------------------- MODULE Luchthaven -------------------------------
EXTENDS Naturals

VARIABLES runway,      \* De startbaan, kan enkel vrij of bezet (voor in of out) zijn
          taxiwayInFreePlaces,   \* De inkomende taxibaan, kan enkele vliegtuigen bevatten
          taxiwayOutFreePlaces,  \* De uitgaande taxibaan, kan enkele vliegtuigen bevatten
          platform,    \* Het platform, kan enkel vrij of bezet zijn
          gatesInUse,  \* Het aantal gates dat bezet is
          land         \* Is er een vliegtuig dat wil landen?

CONSTANTS AmountOfGates,      \* Aantal gates dat aanwezig is in de luchthaven
          TaxiInSize,  \* Aantal plaatsen op de inkomende taxibaan
          TaxiOutSize  \* Aantal plaatsen op de uigaande taxibaan

-----------------------------------------------------------------------------

(* Uitdrukking voor tuple met alle veranderlijken *)
vars == <<runway,taxiwayInFreePlaces,taxiwayOutFreePlaces,platform,gatesInUse,land>>
Status == {"free","out","in"}

(* Begintoestand: lege luchthaven *)
Init == /\ runway = "free"
        /\ taxiwayInFreePlaces = TaxiInSize       \* Aantal vrije plaatsen, dus beginnen op volle capaciteit
        /\ taxiwayOutFreePlaces = TaxiOutSize     \* Aantal vrije plaatsen, dus beginnen op volle capaciteit
        /\ platform = "free"
        /\ gatesInUse = 0
        /\ land = 0

(* AANNAMES:                                                                                     *)
(*  - Vliegtuigen op de taxibaan schuiven automatisch door, enkel eindpunten worden gemodelleerd *)
(*  - Het platform kan slechts door 1 vliegtuig tegelijk betreden worden                         *)
(*  - De taxibaan is duidelijk op te splitsen in een ingaand en uitgaand deel                    *)
(*  - Vliegtuigen reserveren plaatsen op voorhand om blockages te vermijden                      *)

(* Acties *)
NewPlane == /\ land = 0  \* Activating condition: Er zijn geen wachtende vliegtuigen
            /\ land' = 1 \* Er is een nieuw vliegtuig aangekomen
            /\ UNCHANGED <<runway, taxiwayInFreePlaces, taxiwayOutFreePlaces, platform, gatesInUse>>

Arrival == /\ land = 1                   \* Activating condition: Vliegtuig wacht om te landen
           /\ gatesInUse < AmountOfGates \* Activating condition: Er is een gate vrij
           /\ runway = "free"            \* Activating condition: De startbaan is vrij
           /\ taxiwayInFreePlaces >= 1   \* Activating condition: Plaats op inkomende taxibaan (anders startbaan vast!)
           /\ runway' = "in"               \* Bezet de startbaan
           /\ taxiwayInFreePlaces' = taxiwayInFreePlaces - 1   \* Reserveer plaats op de taxibaan
           /\ gatesInUse' = gatesInUse + 1 \* Reserveer gate anders tweede landing voor zelfde gate
           /\ land' = 0                    \* Geef aan dat het landen voltooid is
           /\ UNCHANGED <<platform, taxiwayOutFreePlaces>>

RunwayToTaxi == /\ runway = "in" \* Activating condition: Vliegtuig staat op runway en wil naar taxi
                /\ runway' = "free" \* Er is al plaats op de taxi gereserveerd
                /\ UNCHANGED <<taxiwayInFreePlaces, taxiwayOutFreePlaces, platform, gatesInUse, land>>

TaxiToPlatform == /\ platform = "free"                \* Activating condition: het platform is vrij
                  /\ taxiwayInFreePlaces < TaxiInSize \* Activating condition: Er is een vliegtuig dat het naar een gate wil
                  /\ platform' = "in"           \* Bezet het platform, geef aan dat we op weg zijn naar een gate
                  /\ taxiwayInFreePlaces' = taxiwayInFreePlaces + 1 \* Geef plaats op de taxibaan weer vrij
                  /\ UNCHANGED <<runway, taxiwayOutFreePlaces, gatesInUse, land>>

PlatformToGate == /\ platform = "in" \* Activating condition: Vliegtuig op het platform op weg naar gate
                  /\ platform' = "free"
                  /\ UNCHANGED <<runway, taxiwayInFreePlaces, taxiwayOutFreePlaces, gatesInUse, land>>

GateToPlatform == /\ platform = "free"         \* Activating condition: Platform is vrij
                  /\ taxiwayOutFreePlaces > 0  \* Activating condition: Plaats op uitgaande taxibaan
                  /\ gatesInUse > 0            \* Activating condition: Er zit een vliegtuig klaar in een gate
                  /\ platform' = "out"            \* Bezet het platform, geef aan op weg naar runway
                  /\ taxiwayOutFreePlaces' = taxiwayOutFreePlaces - 1 \* Reserveer plaats op de taxibaan
                  /\ gatesInUse' = gatesInUse - 1 \* Geef gate vrij
                  /\ UNCHANGED <<runway, taxiwayInFreePlaces, land>>

PlatformToTaxi == /\ platform = "out" \* Activating condition: het platform is bezet door uitgaand verkeer
                  /\ platform' = "free" \* Geef platform weer vrij
                  /\ UNCHANGED <<runway, taxiwayInFreePlaces, taxiwayOutFreePlaces, gatesInUse, land>>

TaxiToRunway == /\ runway = "free"                    \* Activating condition: De startbaan is vrij
                /\ taxiwayOutFreePlaces < TaxiOutSize \* Activating condition: Een vliegtuig wacht om op te stijgen
                /\ runway' = "out"        \* Bezet de startbaan, geef aan dat we willen opstijgen
                /\ taxiwayOutFreePlaces' = taxiwayOutFreePlaces + 1 \* Geef plaats vrij op de taxibaan
                /\ UNCHANGED <<taxiwayInFreePlaces, platform, gatesInUse, land>>

TakesOff == /\ runway = "out" \* Activating condition: We willen opstijgen van de startbaan
            /\ runway' = "free" \* Geef de startbaan weer vrij
            /\ UNCHANGED <<taxiwayInFreePlaces, taxiwayOutFreePlaces, platform, gatesInUse, land>>

RejectPlane == /\ land = 1                   \* Activating condition: Er is wachtend verkeer in de lucht
               /\ gatesInUse = AmountOfGates \* Activating condition: Luchthaven is vol
               /\ land' = 0 \* Verwijs het verkeer door naar een andere luchthaven
               /\ UNCHANGED <<runway, taxiwayInFreePlaces, taxiwayOutFreePlaces, platform, gatesInUse>>

(* Samenvatting acties *)
Next == \/ NewPlane
        \/ Arrival
        \/ RunwayToTaxi
        \/ TaxiToPlatform
        \/ PlatformToGate
        \/ GateToPlatform
        \/ PlatformToTaxi
        \/ TaxiToRunway
        \/ TakesOff
        \/ RejectPlane

(* Fairness-voorwaarden *)
Live == /\ SF_vars(NewPlane)
        /\ SF_vars(Arrival)
        /\ SF_vars(RunwayToTaxi)
        /\ SF_vars(TaxiToPlatform)
        /\ SF_vars(PlatformToGate)
        /\ SF_vars(GateToPlatform)
        /\ SF_vars(PlatformToTaxi)
        /\ SF_vars(TaxiToRunway)
        /\ SF_vars(TakesOff)
        /\ SF_vars(RejectPlane)

(* Specificatie *)
Spec == Init /\ [][Next]_vars /\ Live
-----------------------------------------------------------------------------
(* Definitie verifcatie-eigenschappen *)

(* Typeinvariant *)
Types == /\ runway \in Status
         /\ taxiwayInFreePlaces \in (0 .. TaxiInSize)
         /\ taxiwayOutFreePlaces \in (0 .. TaxiOutSize)
         /\ platform \in Status
         /\ gatesInUse \in (0 .. AmountOfGates)
         /\ land \in {0,1}

(* Verhinderen van deadlocks *)
RunwayAlwaysBecomesFreeEventually     == []<>((runway = "out" \/ runway = "in") ~> (runway = "free"))
PlatformAlwaysBecomesFreeEventually   == []<>((platform = "out" \/ platform = "in") ~> (platform = "free"))
TaxiwayInAlwaysBecomesFreeEventually  == []<>((taxiwayInFreePlaces = TaxiInSize) ~> (taxiwayInFreePlaces < TaxiInSize))
TaxiwayOutAlwaysBecomesFreeEventually == []<>((taxiwayOutFreePlaces = TaxiOutSize) ~> (taxiwayOutFreePlaces < TaxiOutSize))
GatesAlwaysBecomesFreeEventually      == []<>((gatesInUse = AmountOfGates) ~> (gatesInUse < AmountOfGates))

(* Botsingen voor een-vliegtuig-zones *)
NoPlatformCrashes == /\ (ENABLED<<TaxiToPlatform>>_vars => ~(ENABLED<<PlatformToTaxi>>_vars))
                     /\ (ENABLED<<PlatformToTaxi>>_vars => ~(ENABLED<<TaxiToPlatform>>_vars))
NoRunwayCrashes ==   /\ (ENABLED<<Arrival>>_vars        => ~(ENABLED<<TakesOff>>_vars))
                     /\ (ENABLED<<TakesOff>>_vars       => ~(ENABLED<<Arrival>>_vars))

(* Overlopen van buffers *)
PlanesDontArriveWhenFull              == (gatesInUse = AmountOfGates) => ~(ENABLED<<Arrival>>_vars)
PlanesDontArriveWhenTaxiinIsFull      == (taxiwayInFreePlaces = 0)    => ~(ENABLED<<Arrival>>_vars)
PlanesDontLeaveGatesWhenTaxioutIsFull == (taxiwayOutFreePlaces = 0)   => ~(ENABLED<<GateToPlatform>>_vars)

-----------------------------------------------------------------------------
(* De te verifieren eigenschappen *)

(* Typeinvariant *)
THEOREM Spec => []Types     \* Type invariantie opleggen

(* Verhinderen van deadlocks *)
THEOREM Spec => RunwayAlwaysBecomesFreeEventually
THEOREM Spec => PlatformAlwaysBecomesFreeEventually
THEOREM Spec => TaxiwayInAlwaysBecomesFreeEventually
THEOREM Spec => TaxiwayOutAlwaysBecomesFreeEventually
THEOREM Spec => GatesAlwaysBecomesFreeEventually

(* Botsingen voor een-vliegtuig-zones *)
THEOREM Spec => []NoPlatformCrashes
THEOREM Spec => []NoRunwayCrashes

(* Overlopen van buffers *)
THEOREM Spec => []PlanesDontArriveWhenFull
THEOREM Spec => []PlanesDontArriveWhenTaxiinIsFull
THEOREM Spec => []PlanesDontLeaveGatesWhenTaxioutIsFull
=============================================================================
