

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Scanner;

/**
 * RandomPersonGenerator has the ability to generate random names. When using a seed, 
 * the same names are generated on every run. By default, no seed is used.
 * The generator is implemented as a singleton with
 * a static factory. This is done to reduce the overhead of loading multiple
 * instances of the name list in memory.
 * 
 * @author Bart Mesuere
 * 
 */
public class RandomPersonGenerator {
	// the only instance used
	private static final RandomPersonGenerator INSTANCE = new RandomPersonGenerator();
	
	// data files
	private static final String FIRSTNAMES = "data/firstnames.txt";
	private static final String LASTNAMES = "data/lastnames.txt";
	private static final String PLACES = "data/places.txt";
	
	// random generator
	private final Random random;
	
	// data lists
	private final List<String> firstNames;
	private final List<String> lastNames;
	private final List<String> places;
	
	private int id;
	
	/**
	 * private constructor of RandomPersonGenerator. Initializes the random
	 * generator and loads the names into memory.
	 */
	private RandomPersonGenerator() {
		// initialize the random generator
		random = new Random();
		
		// initialize lists
		firstNames = new ArrayList<String>();
		lastNames = new ArrayList<String>();
		places = new ArrayList<String>();
		
		// fill the lists
		readFile(new File(FIRSTNAMES), firstNames);
		readFile(new File(LASTNAMES), lastNames);
		readFile(new File(PLACES), places);
		
		// set id
		id = 0;
	}
	
	/**
	 * readFile adds the content of the given file to the given list. Each line
	 * in the file is added as a String.
	 */
	private void readFile(File file, List<String> list) {
		try {
			Scanner scanner = new Scanner(file);
			while (scanner.hasNext()) {
				list.add(scanner.nextLine());
			}
		} catch (FileNotFoundException e) {
			System.err.println("This file could not be found: " + file.getPath());
			e.printStackTrace();
		}
	}
	
	/**
	 * Returns the one and only instance of the RandomNameGenerator. If you want
	 * to reset the generator (e.g. between experiments), use the reset method
	 * instead.
	 * 
	 * @return The only instance of RandomNameGenerator
	 */
	public static RandomPersonGenerator getInstance() {
		return INSTANCE;
	}
	
	/**
	 * Sets a new seed and resets the random generator. Since there is only one
	 * instance of this class, all instances are reset.
	 * 
	 * @param seed
	 *            A random generator seed
	 */
	public void setSeed(long seed) {
		random.setSeed(seed);
	}
	
	/**
	 * Returns an incremental id
	 * 
	 * @return an incremental id
	 */
	private int getId() {
		return id++;
	}
	
	/**
	 * Returns a random first name.
	 * 
	 * @return a random first name
	 */
	private String getRandomFirstName() {
		return firstNames.get(random.nextInt(firstNames.size()));
	}
	
	/**
	 * Returns a random last name.
	 * 
	 * @return a random last name
	 */
	private String getRandomLastName() {
		return lastNames.get(random.nextInt(lastNames.size()));
	}
	
	/**
	 * Returns a random place.
	 * 
	 * @return a random place
	 */
	private String getRandomPlace() {
		return places.get(random.nextInt(places.size()));
	}
	
	/**
	 * Returns a random age (with lower probability for high ages)
	 * 
	 * @return a random age
	 */
	
	private String getRandomAge() {
		// determine category of age
		int nr = random.nextInt(1000);
		
		// age <= 80 (96% probability)
		if (nr < 960) {
			return "" + random.nextInt(81);
		}
		// 80 < age <= 90 (3.5% probability)
		else if (nr < 995) {
			return "" + (81 + random.nextInt(10));
		}
		// 90 < age <= 95 (0.4% probability)
		else if (nr < 999) {
			return "" + (91 + random.nextInt(5));
		}
		// 96 < age <= 100 (0.1% probability)
		else {
			return "" + (96 + random.nextInt(5));
		}
	}
	
	/**
	 * Returns a random phone number of the form 04xx xx xx xx
	 * 
	 * @return a random phone number
	 */
	private String getRandomPhoneNumber() {
		StringBuilder stringBuilder = new StringBuilder(13);
		stringBuilder.append("04");
		stringBuilder.append(random.nextInt(10));
		stringBuilder.append(random.nextInt(10));
		stringBuilder.append(' ');
		stringBuilder.append(random.nextInt(10));
		stringBuilder.append(random.nextInt(10));
		stringBuilder.append(' ');
		stringBuilder.append(random.nextInt(10));
		stringBuilder.append(random.nextInt(10));
		stringBuilder.append(' ');
		stringBuilder.append(random.nextInt(10));
		stringBuilder.append(random.nextInt(10));
		return stringBuilder.toString();
	}
	
	/**
	 * Returns a random person. A person consists of an Id, a first name, last
	 * name, phone number, place and age. These strings are returned as a String
	 * array. The first array element contains the first name, the second
	 * element the last name, the third element the phone number, the fourth
	 * element a place and the fifth element the year of birth.
	 * 
	 * @return an array containing the ID, first name, last name, phone number,
	 *         place and age of a person
	 */
	public String[] getRandomPerson() {
		String[] person = new String[6];
		person[0] = "" + getId();
		person[1] = getRandomFirstName();
		person[2] = getRandomLastName();
		person[3] = getRandomPhoneNumber();
		person[4] = getRandomPlace();
		person[5] = getRandomAge();
		return person;
	}
	
}
