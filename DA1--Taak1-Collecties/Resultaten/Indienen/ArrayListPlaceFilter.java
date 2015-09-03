import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;

/**
 *
 * @author tnnaesse
 */
public class ArrayListPlaceFilter implements PlaceFilter {

	private ArrayList<NormalPerson> personen;
	private Collection<String> verwijderde;
	private Iterator<NormalPerson> iterator;

	public ArrayListPlaceFilter() {
		// Initieert de variabelen
		personen = new ArrayList();
		verwijderde = new ArrayList();
	}

	public void addPerson(String[] person) {
		// Voegt een persoon toe aan de ArrayList
		personen.add(new NormalPerson(person));
	}

	public Collection<String> removeInhabitants(String city) {
		/*
		 * Itereert over de lijst en vanaf hij een persoon tegenkomt waarvan
		 * de naam van zijn gemeente gelijk is aan de opgegeven gemeente voegt
		 * hij deze toe aan een lijst en verwijdert hij deze uit de oorspronke-
		 * elijke lijst.
		 */
		iterator = personen.iterator();
		while (iterator.hasNext()) {
			NormalPerson temp = iterator.next();
			if (city.equals(temp.getGemeente())) {
				verwijderde.add(temp.getID());
				iterator.remove();
			}
		}
		return verwijderde;
	}
}
