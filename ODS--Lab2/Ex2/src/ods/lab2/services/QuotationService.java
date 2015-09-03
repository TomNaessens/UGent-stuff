package ods.lab2.services;

import javax.persistence.EntityManager;

import ods.lab2.entities.Quotation;

public class QuotationService {

	public Quotation getQuotationById(Long id) {
		EntityManager entityManager = EMF.get().createEntityManager();

		Quotation quotation = null;

		try {
			quotation = entityManager.find(Quotation.class, id);
		} finally {
			entityManager.close();
		}

		return quotation;
	}

}
