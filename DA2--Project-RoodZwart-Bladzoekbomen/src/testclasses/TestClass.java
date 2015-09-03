/**
 * Testklasse: kan een stuk eleganter.
 * 
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package testclasses;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Random;
import redblacktrees.AbstractRBTree;
import redblacktrees.MyVertex;
import redblacktrees.Tree1;
import redblacktrees.Tree2;
import redblacktrees.Tree3;
import redblacktrees.Tree4;
import redblacktrees.Tree5;
import redblacktrees.Tree6;
import redblacktrees.Tree7;

public class TestClass {

	private static final int MIN_TOPS = 0;
	private static final int MAX_TOPS = 2000000;
	private static final int INCREMENT = 100000;
	private static final int NUMBER_OF_TESTS_FOR_ONE_INPUT = 5;

	public static void main(String[] args) {
		tree1AddRandom();
		tree1AddOrdered();
		tree1Contains();
		tree1Remove();
		tree1Iterate();
		System.out.println("");

		tree2AddRandom();
		tree2AddOrdered();
		tree2Contains();
		tree2Remove();
		tree2Iterate();
		System.out.println("");

		tree3AddRandom();
		tree3AddOrdered();
		tree3Contains();
		tree3Remove();
		tree3Iterate();
		System.out.println("");

		tree4AddRandom();
		tree4AddOrdered();
		tree4Contains();
		tree4Iterate();
		System.out.println("");

		tree5AddRandom();
		tree5AddOrdered();
		tree5Contains();
		tree5Iterate();
		System.out.println("");

		tree6AddRandom();
		tree6AddOrdered();
		tree6Contains();
		tree6Iterate();
		System.out.println("");

		tree7AddRandom();
		tree7AddOrdered();
		tree7Contains();
		tree7Iterate();

	}

	public static void tree1AddRandom() {
		System.out.println("Tree 1\tAdd()\tRandom volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree1AddOrdered() {
		System.out.println("Tree1\tAdd()\tGeordende volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree1 tree = new Tree1();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree1 tree = new Tree1();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree1Contains() {
		System.out.println("Tree1\tcontains()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree1Remove() {
		System.out.println("Tree1\tremove()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);
				removeElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				removeElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);
				removeElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				removeElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree1Iterate() {
		System.out.println("Tree1\titerator()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree1 tree = new Tree1();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree2AddRandom() {
		System.out.println("Tree2\tAdd()\tRandom volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree2AddOrdered() {
		System.out.println("Tree2\tAdd()\tGeordende volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree2 tree = new Tree2();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree2 tree = new Tree2();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree2Contains() {
		System.out.println("Tree2\tcontains()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree2Remove() {
		System.out.println("Tree2\tremove()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);
				removeElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				removeElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);
				removeElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				removeElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree2Iterate() {
		System.out.println("Tree2\titerator()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree2 tree = new Tree2();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree3AddRandom() {
		System.out.println("Tree 3\tAdd()\tRandom volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree3AddOrdered() {
		System.out.println("Tree3\tAdd()\tGeordende volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree3 tree = new Tree3();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree3 tree = new Tree3();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree3Contains() {
		System.out.println("Tree3\tcontains()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree3Remove() {
		System.out.println("Tree3\tremove()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);
				removeElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				removeElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);
				removeElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				removeElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree3Iterate() {
		System.out.println("Tree3\titerator()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree3 tree = new Tree3();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree4AddRandom() {
		System.out.println("Tree4\tAdd()\tRandom volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree4AddOrdered() {
		System.out.println("Tree4\tAdd()\tGeordende volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree4 tree = new Tree4();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree4 tree = new Tree4();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree4Contains() {
		System.out.println("Tree4\tcontains()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree4Iterate() {
		System.out.println("Tree4\titerator()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree4 tree = new Tree4();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree5AddRandom() {
		System.out.println("Tree5\tAdd()\tRandom volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree5AddOrdered() {
		System.out.println("Tree5\tAdd()\tGeordende volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree5 tree = new Tree5();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree5 tree = new Tree5();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree5Contains() {
		System.out.println("Tree5\tcontains()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree5Iterate() {
		System.out.println("Tree5\titerator()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree5 tree = new Tree5();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree6AddRandom() {
		System.out.println("Tree6\tAdd()\tRandom volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree6AddOrdered() {
		System.out.println("Tree6\tAdd()\tGeordende volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree6 tree = new Tree6();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree6 tree = new Tree6();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree6Contains() {
		System.out.println("Tree6\tcontains()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree6Iterate() {
		System.out.println("Tree6\titerator()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree6 tree = new Tree6();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree7AddRandom() {
		System.out.println("Tree7\tAdd()\tRandom volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree7AddOrdered() {
		System.out.println("Tree7\tAdd()\tGeordende volgorde:");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree7 tree = new Tree7();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createOrderedList(number_of_tops);
				Tree7 tree = new Tree7();

				long tijd = System.currentTimeMillis();
				addElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree7Contains() {
		System.out.println("Tree7\tcontains()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);
				containsElements(tree, arrayList);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				containsElements(tree, arrayList);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void tree7Iterate() {
		System.out.println("Tree7\titerator()");
		for (int number_of_tops = MIN_TOPS; number_of_tops <= MAX_TOPS; number_of_tops += INCREMENT) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}

		for (int number_of_tops = 2500000; number_of_tops <= 7500000; number_of_tops += 500000) {
			System.out.print("Input:\t" + number_of_tops + "\tMs:");

			// WARM UP
			for (int warm_up = 0; warm_up < 3; warm_up++) {
				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);
				iterateElements(tree);

				tree = null;
				System.gc();
			}

			// REAL TESTING
			for (int i = 0; i < NUMBER_OF_TESTS_FOR_ONE_INPUT; i++) {

				ArrayList<Integer> arrayList = createList(number_of_tops);
				Tree7 tree = new Tree7();

				addElements(tree, arrayList);

				long tijd = System.currentTimeMillis();
				iterateElements(tree);
				System.out.print("\t" + (System.currentTimeMillis() - tijd));

				tree = null;
				System.gc();
			}

			System.out.println("");
		}
	}

	public static void writeToDot(MyVertex root) {
		DotWriter dotWriter = new DotWriter();
		dotWriter.addNode(root);
		dotWriter.closeWriter();
	}

	public static void testTree(MyVertex root) {
		TreeTester treeTester = new TreeTester();
		treeTester.test(root);
	}

	public static ArrayList<Integer> createList(int max) {
		ArrayList<Integer> arrayList = new ArrayList<Integer>();
		Random random = new Random();
		for (int i = 0; i < max; i++) {
			arrayList.add(random.nextInt(1000000000));
		}
		return arrayList;
	}

	public static ArrayList<Integer> createOrderedList(int max) {
		ArrayList<Integer> arrayList = new ArrayList<Integer>();
		for (int i = 0; i < max; i++) {
			arrayList.add(i);
		}
		return arrayList;
	}

	public static void addElements(AbstractRBTree tree, ArrayList<Integer> arrayList) {
		for (int getal : arrayList) {
			tree.add(getal);
		}
	}

	public static void containsElements(AbstractRBTree tree, ArrayList<Integer> arrayList) {
		for (int getal : arrayList) {
			tree.contains(getal);
		}
	}

	public static void iterateElements(AbstractRBTree tree) {
		Iterator<Integer> iterator = tree.iterator();
		while (iterator.hasNext()) {
			iterator.next();
		}
	}

	public static void removeElements(AbstractRBTree tree, ArrayList<Integer> arrayList) {
		for (int getal : arrayList) {
			tree.remove(getal);
		}
	}
}
