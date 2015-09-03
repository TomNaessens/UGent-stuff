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
import joldespice.components.linear.Resistor;

public class ResistorIcon extends IconPainter {

	public ResistorIcon() {
		super(24);
	}

	@Override
	public void paintIcon(Component c, Graphics g, int x, int y) {
		Graphics2D g2 = (Graphics2D) g.create();

		super.paintIcon(c,g2,x,y);
		
		g2.drawLine(-12, 0, -10, -5); // Up!
		g2.drawLine(-10, -5, -6, 5); // Down!
		g2.drawLine(-6, 5, -2, -5); // Back up!
		g2.drawLine(-2, -5, 2, 5); // Back down!
		g2.drawLine(2, 5, 6, -5); // Get up!
		g2.drawLine(6, -5, 10, 5); // Get down!
		g2.drawLine(10, 5, 12, 0); // And up again!
	}

	@Override
	public String getComponent() {
		return "Resistor";
	}
}
