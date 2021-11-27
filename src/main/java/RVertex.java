/*******************************************************************************
 * Copyright (c) 2004, 2010 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/


import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * A vertex representation for the ShortestPathRouting. Vertices are either one
 * of four corners on an <code>Obstacle</code>(Rectangle), or one of the two end
 * points of a <code>Path</code>.
 * 
 * This class is not intended to be subclassed.
 * 
 * @author Whitney Sorenson
 * @since 3.0
 */
class RVertex extends RPoint {

	// constants for the vertex type
	static final int NOT_SET = 0;
	static final int INNIE = 1;
	static final int OUTIE = 2;

	// for shortest path
	List neighbors;
	boolean isPermanent = false;
	RVertex label;
	double cost = 0;

	// for routing
	int nearestObstacle = 0;
	double offset = 0;
	int type = NOT_SET;
	int count = 0;
	int totalCount = 0;
	RObstacle obs;
	List paths;
	boolean nearestObstacleChecked = false;
	Map cachedCosines;
	int positionOnObstacle = -1;

	private int origX, origY;

	/**
	 * Creates a new Vertex with the given x, y position and on the given
	 * obstacle.
	 * 
	 * @param x
	 *            x point
	 * @param y
	 *            y point
	 * @param obs
	 *            obstacle - can be null
	 */
	RVertex(int x, int y, RObstacle obs) {
		super(x, y);
		origX = x;
		origY = y;
		this.obs = obs;
	}

	/**
	 * Creates a new Vertex with the given point position and on the given
	 * obstacle.
	 * 
	 * @param p
	 *            the point
	 * @param obs
	 *            obstacle - can be null
	 */
	RVertex(RPoint p, RObstacle obs) {
		this(p.x, p.y, obs);
	}

	/**
	 * Adds a path to this vertex, calculates angle between two segments and
	 * caches it.
	 * 
	 * @param path
	 *            the path
	 * @param start
	 *            the segment to this vertex
	 * @param end
	 *            the segment away from this vertex
	 */
	void addPath(RPath path, RSegment start, RSegment end) {
		if (paths == null) {
			paths = new ArrayList();
			cachedCosines = new HashMap();
		}
		if (!paths.contains(path))
			paths.add(path);
		cachedCosines.put(path, new Double(start.cosine(end)));
	}

	/**
	 * Creates a point that represents this vertex offset by the given amount
	 * times the offset.
	 * 
	 * @param modifier
	 *            the offset
	 * @return a Point that has been bent around this vertex
	 */
	RPoint bend(int modifier) {
		RPoint point = new RPoint(x, y);
		if ((positionOnObstacle & RPositionConstants.NORTH) > 0)
			point.y -= modifier * offset;
		else
			point.y += modifier * offset;
		if ((positionOnObstacle & RPositionConstants.EAST) > 0)
			point.x += modifier * offset;
		else
			point.x -= modifier * offset;
		return point;
	}

	/**
	 * Resets all fields on this Vertex.
	 */
	void fullReset() {
		totalCount = 0;
		type = NOT_SET;
		count = 0;
		cost = 0;
		offset = getSpacing();
		nearestObstacle = 0;
		label = null;
		nearestObstacleChecked = false;
		isPermanent = false;
		if (neighbors != null)
			neighbors.clear();
		if (cachedCosines != null)
			cachedCosines.clear();
		if (paths != null)
			paths.clear();
	}

	/**
	 * Returns a Rectangle that represents the region around this vertex that
	 * paths will be traveling in.
	 * 
	 * @param extraOffset
	 *            a buffer to add to the region.
	 * @return the rectangle
	 */
	RRectangle getDeformedRectangle(int extraOffset) {
		RRectangle rect = new RRectangle(0, 0, 0, 0);

		if ((positionOnObstacle & RPositionConstants.NORTH) > 0) {
			rect.y = y - extraOffset;
			rect.height = origY - y + extraOffset;
		} else {
			rect.y = origY;
			rect.height = y - origY + extraOffset;
		}
		if ((positionOnObstacle & RPositionConstants.EAST) > 0) {
			rect.x = origX;
			rect.width = x - origX + extraOffset;
		} else {
			rect.x = x - extraOffset;
			rect.width = origX - x + extraOffset;
		}

		return rect;
	}

	private int getSpacing() {
		if (obs == null)
			return 0;
		return obs.getSpacing();
	}

	/**
	 * Grows this vertex by its offset to its maximum size.
	 */
	void grow() {
		int modifier;

		if (nearestObstacle == 0)
			modifier = totalCount * getSpacing();
		else
			modifier = (nearestObstacle / 2) - 1;

		if ((positionOnObstacle & RPositionConstants.NORTH) > 0)
			y -= modifier;
		else
			y += modifier;
		if ((positionOnObstacle & RPositionConstants.EAST) > 0)
			x += modifier;
		else
			x -= modifier;
	}

	/**
	 * Shrinks this vertex to its original size.
	 */
	void shrink() {
		x = origX;
		y = origY;
	}

	/**
	 * Updates the offset of this vertex based on its shortest distance.
	 */
	void updateOffset() {
		if (nearestObstacle != 0)
			offset = ((nearestObstacle / 2) - 1) / totalCount;
	}

	/**
	 * @see org.eclipse.draw2d.geometry.RPoint#toString()
	 */
	public String toString() {
		return "V(" + origX + ", " + origY + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
	}

}
