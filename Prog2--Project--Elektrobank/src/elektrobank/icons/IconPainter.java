/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.icons;

import java.awt.BasicStroke;
import java.awt.Color;
import java.awt.Component;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;
import javax.swing.Icon;

public abstract class IconPainter implements Icon {

	int length;
	double angle;
	int iconWidth;
	Color color;
	float thickness;

	public IconPainter(int iconWidth) {
		this.iconWidth = iconWidth; // Wordt ook meegegeven aangezien niet alle icons even breedt zijn
		thickness = 1; // Standaard is 1
	}

	public void paintIcon(Component c, Graphics g, int x, int y) {
		Graphics2D g2 = (Graphics2D) g;
		g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
		g2.setColor(color);
		g2.setStroke(new BasicStroke(thickness));
		g2.translate(x, y);
		g2.translate(getIconWidth() / 2, getIconHeight() / 2);
		g2.rotate(angle);

		if (length > iconWidth) {
			g2.drawLine(-length / 2, 0, -iconWidth / 2, 0);
			g2.drawLine(length / 2, 0, iconWidth / 2, 0);
		}
	}

	public int getIconWidth() {
		return 60;
	}

	public int getIconHeight() {
		return 20;
	}

	public String getComponent() {
		return null;
	}

	public void setColor(Color color) {
		this.color = color;
	}

	public void setAngle(double angle) {
		this.angle = angle;
	}

	public void setLength(int length) {
		this.length = length;
	}

	public void setThickness(float thickness) {
		if (thickness < 1) {
			this.thickness = 1;
		} else {
			this.thickness = thickness;
		}
	}
}
