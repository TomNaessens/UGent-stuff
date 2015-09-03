

/**
 * Deze klasse heeft als enig doel na te gaan of alle gevraagde klassen
 * een default-constructor (zonder parameters) hebben en of de gevraagde klassen
 * inderdaad de gegeven interfaces implementeren.
 * Op Indianio wordt deze klasse automatisch mee gecompileerd.
 * Het kan dus zijn dat je op Indianio foutmeldingen krijgt i.v.m. deze klasse!
 */
public class ConstructorTest {

	public static void main(String[] args) {
		PlaceFilter filter1 = new ArrayListPlaceFilter();
		PlaceFilter filter2 = new LinkedListPlaceFilter();
		InitialsCounter counter1 = new ListInitialsCounter();
		InitialsCounter counter2 = new HashMapInitialsCounter();
		PhoneBook book = new MyPhoneBook();
		OldestPeopleFinder finder = new MyOldestPeopleFinder();


	}
}
