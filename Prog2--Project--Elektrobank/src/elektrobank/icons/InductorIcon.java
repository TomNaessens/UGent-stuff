/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.icons;

import java.awt.Component;
import java.awt.Graphics;
import java.awt.Graphics2D;
import joldespice.components.differential.Inductor;

public class InductorIcon extends IconPainter {

	public InductorIcon() {
		super(24);
	}

	@Override
	public void paintIcon(Component c, Graphics g, int x, int y) {
		Graphics2D g2 = (Graphics2D) g.create();

		super.paintIcon(c,g2,x,y);

		g2.drawArc(-12, -5, 10, 10, -45, 235); // Cirkelstuk links
		g2.drawArc(-5, -5, 10, 10, -45, 270); // Cirkelstuk midden
		g2.drawArc(2, -5, 10, 10, 0, 230); // Cirkelstuk rechts
	}

	@Override
	public String getComponent() {
		return  "Inductor";
	}
}
