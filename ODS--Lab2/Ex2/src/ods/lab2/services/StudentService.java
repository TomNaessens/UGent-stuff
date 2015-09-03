package ods.lab2.services;

import java.util.ArrayList;
import java.util.List;

import javax.persistence.EntityManager;
import javax.persistence.NoResultException;
import javax.persistence.Query;

import ods.lab2.entities.Student;
import ods.lab2.utils.Globals;

public class StudentService {

	public Student getStudentById(Long id) {
		EntityManager entityManager = EMF.get().createEntityManager();

		Student student = null;

		try {
			student = entityManager.find(Student.class, id);
		} finally {
			entityManager.close();
		}

		return student;
	}

	public Student getStudentByName(String name, String surname) {
		EntityManager entityManager = EMF.get().createEntityManager();

		Student resultingStudent = null;

		try {
			Query query = entityManager.createQuery("SELECT x FROM Student" + " x " + "WHERE x.name = :name "
					+ "AND x.surname = :surname");

			query.setParameter("name", name);
			query.setParameter("surname", surname);

			resultingStudent = (Student) query.getSingleResult();
		} catch (NoResultException ex) {
			// No result? Return null.
			return null;
		} finally {
			entityManager.close();
		}

		return resultingStudent;
	}

	public List<Student> getGroupOfStudentsByID(int groupnumber) {
		EntityManager entityManager = EMF.get().createEntityManager();

		List<Student> resultingStudents = new ArrayList<Student>();

		try {
			Query query = entityManager.createQuery("SELECT x FROM " + "Student" + " x "
					+ "WHERE x.groupnumber = :groupnumber");

			query.setParameter("groupnumber", groupnumber);

			resultingStudents = (List<Student>) query.getResultList();
		} finally {
			entityManager.close();
		}

		return resultingStudents;

	}

	public List<Student> getAllStudents() {
		EntityManager entityManager = EMF.get().createEntityManager();

		List<Student> resultingStudents = new ArrayList<Student>();

		try {
			Query query = entityManager.createQuery("SELECT x FROM " + "Student" + " x");
			resultingStudents = (List<Student>) query.getResultList();
		} finally {
			entityManager.close();
		}

		return resultingStudents;
	}

	// Throws a NumberFormatException if the Strings can't be parsed into an int
	public void addStudent(String name, String surname, String groupnumber, String checksum)
			throws NumberFormatException {
		EntityManager entityManager = EMF.get().createEntityManager();

		// Create a new student
		Student student = new Student();

		// Set the attributes
		student.setName(name);
		student.setSurname(surname);
		student.setGroupnumber((groupnumber == null) ? Globals.GROUPID : Integer.parseInt(groupnumber));
		student.setChecksum((checksum == null) ? Globals.CHECKSUM : Integer.parseInt(checksum));

		try {
			entityManager.getTransaction().begin();
			entityManager.persist(student);
			entityManager.getTransaction().commit();
		} finally {
			entityManager.close();
		}

	}

	public void editStudent(String name, String surname, Integer groupnumber, Integer checksum, Student student) {

		EntityManager entityManager = EMF.get().createEntityManager();

		try {

			student.setName(name);
			student.setSurname(surname);
			student.setGroupnumber(groupnumber);
			student.setChecksum(checksum);

			entityManager.getTransaction().begin();
			entityManager.merge(student);
			entityManager.getTransaction().commit();

		} finally {
			entityManager.close();
		}

	}

	public void removeStudentByID(long id) {
		EntityManager entityManager = EMF.get().createEntityManager();

		try {
			entityManager.getTransaction().begin();
			entityManager.remove(entityManager.find(Student.class, id));
			entityManager.getTransaction().commit();
		} finally {
			entityManager.close();
		}
	}

	public void removeStudentByName(String name, String surname, int checksum) {
		EntityManager entityManager = EMF.get().createEntityManager();

		try {
			entityManager.getTransaction().begin();

			Query query = entityManager.createQuery("DELETE FROM " + "Student" + " x " + "WHERE x.name = :name "
					+ "AND x.surname = :surname " + "AND x.checksum = :checksum");

			query.setParameter("name", name);
			query.setParameter("surname", surname);
			query.setParameter("checksum", checksum);

			query.executeUpdate();

			entityManager.getTransaction().commit();
		} finally {
			entityManager.close();
		}
	}

	public void removeGroup(int groupnumber) {
		EntityManager entityManager = EMF.get().createEntityManager();

		try {
			entityManager.getTransaction().begin();

			// The assignment didn't specify a checksum check here, but adding
			// one isn't hard: it is only needed to add an AND to the clause.
			Query query = entityManager.createQuery("DELETE FROM " + "Student" + " x "
					+ "WHERE x.groupnumber = :groupnumber");

			query.setParameter("groupnumber", groupnumber);

			query.executeUpdate();

			entityManager.getTransaction().commit();
		} finally {
			entityManager.close();
		}
	}
}
