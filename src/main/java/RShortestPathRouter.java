/*******************************************************************************
 * Copyright (c) 2004, 2010 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 * IBM Corporation - initial API and implementation
 *******************************************************************************/


import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

/**
 * Bends a collection of {@link RPath Paths} around rectangular obstacles. This
 * class maintains a list of paths and obstacles. Updates can be made to the
 * paths and/or obstacles, and then an incremental solve can be invoked.
 * <P>
 * The algorithm will attempt to find the shortest non-intersecting path between
 * each path's start and end points. Once all paths have been found, they will
 * be offset based on how many paths bend around the same corner of each
 * obstacle.
 * <P>
 * The worst-case performance of this algorithm is p * s * n^2, where p is the
 * number of paths, n is the number of obstacles, and s is the average number of
 * segments in each path's final solution.
 * <P>
 * This class is not intended to be subclassed.
 * 
 * @author Whitney Sorenson
 * @author Randy Hudson
 * @since 3.0
 */
public class RShortestPathRouter {

	/**
	 * A stack of Paths.
	 */
	static class PathStack extends ArrayList {

		RPath pop() {
			return (RPath) remove(size() - 1);
		}

		void push(RPath path) {
			add(path);
		}
	}

	/**
	 * The number of times to grow obstacles and test for intersections. This is
	 * a tradeoff between performance and quality of output.
	 */
	private static final int NUM_GROW_PASSES = 2;

	private int spacing = 4;
	private boolean growPassChangedObstacles;
	private List orderedPaths;
	private Map pathsToChildPaths;

	private PathStack stack;
	private List subPaths;

	private List userObstacles;
	private List userPaths;
	private List workingPaths;

	/**
	 * Creates a new shortest path routing.
	 */
	public RShortestPathRouter() {
		userPaths = new ArrayList();
		workingPaths = new ArrayList();
		pathsToChildPaths = new HashMap();
		userObstacles = new ArrayList();
	}

	/**
	 * Adds an obstacle with the given bounds to the obstacles.
	 * 
	 * @param rect
	 *            the bounds of this obstacle
	 * @return <code>true</code> if the added obstacle has dirtied one or more
	 *         paths
	 */
	public boolean addObstacle(RRectangle rect) {
		return internalAddObstacle(new RObstacle(rect, this));
	}

	/**
	 * Adds a path to the routing.
	 * 
	 * @param path
	 *            the path to add.
	 */
	public void addPath(RPath path) {
		userPaths.add(path);
		workingPaths.add(path);
	}

	/**
	 * Fills the point lists of the Paths to the correct bent points.
	 */
	private void bendPaths() {
		for (int i = 0; i < orderedPaths.size(); i++) {
			RPath path = (RPath) orderedPaths.get(i);
			RSegment segment = null;
			path.points.addPoint(new RPoint(path.start.x, path.start.y));
			for (int v = 0; v < path.grownSegments.size(); v++) {
				segment = (RSegment) path.grownSegments.get(v);
				RVertex vertex = segment.end;

				if (vertex != null && v < path.grownSegments.size() - 1) {
					if (vertex.type == RVertex.INNIE) {
						vertex.count++;
						path.points.addPoint(vertex.bend(vertex.count));
					} else {
						path.points.addPoint(vertex.bend(vertex.totalCount));
						vertex.totalCount--;
					}
				}
			}
			path.points.addPoint(new RPoint(path.end.x, path.end.y));
		}
	}

	/**
	 * Checks a vertex to see if its offset should shrink
	 * 
	 * @param vertex
	 *            the vertex to check
	 */
	private void checkVertexForIntersections(RVertex vertex) {
		if (vertex.nearestObstacle != 0 || vertex.nearestObstacleChecked)
			return;
		int sideLength, x, y;

		sideLength = 2 * (vertex.totalCount * getSpacing()) + 1;

		if ((vertex.positionOnObstacle & RPositionConstants.NORTH) > 0)
			y = vertex.y - sideLength;
		else
			y = vertex.y;
		if ((vertex.positionOnObstacle & RPositionConstants.EAST) > 0)
			x = vertex.x;
		else
			x = vertex.x - sideLength;

		RRectangle r = new RRectangle(x, y, sideLength, sideLength);

		int xDist, yDist;

		for (int o = 0; o < userObstacles.size(); o++) {
			RObstacle obs = (RObstacle) userObstacles.get(o);
			if (obs != vertex.obs && r.intersects(obs)) {
				int pos = obs.getPosition(vertex);
				if (pos == 0)
					continue;

				if ((pos & RPositionConstants.NORTH) > 0)
					// use top
					yDist = obs.y - vertex.y;
				else
					// use bottom
					yDist = vertex.y - obs.bottom() + 1;
				if ((pos & RPositionConstants.EAST) > 0)
					// use right
					xDist = vertex.x - obs.right() + 1;
				else
					// use left
					xDist = obs.x - vertex.x;

				if (Math.max(xDist, yDist) < vertex.nearestObstacle
						|| vertex.nearestObstacle == 0) {
					vertex.nearestObstacle = Math.max(xDist, yDist);
					vertex.updateOffset();
				}

			}
		}

		vertex.nearestObstacleChecked = true;
	}

	/**
	 * Checks all vertices along paths for intersections
	 */
	private void checkVertexIntersections() {
		for (int i = 0; i < workingPaths.size(); i++) {
			RPath path = (RPath) workingPaths.get(i);

			for (int s = 0; s < path.segments.size() - 1; s++) {
				RVertex vertex = ((RSegment) path.segments.get(s)).end;
				checkVertexForIntersections(vertex);
			}
		}
	}

	/**
	 * Frees up fields which aren't needed between invocations.
	 */
	private void cleanup() {
		for (int i = 0; i < workingPaths.size(); i++) {
			RPath path = (RPath) workingPaths.get(i);
			path.cleanup();
		}
	}

	/**
	 * Counts how many paths are on given vertices in order to increment their
	 * total count.
	 */
	private void countVertices() {
		for (int i = 0; i < workingPaths.size(); i++) {
			RPath path = (RPath) workingPaths.get(i);
			for (int v = 0; v < path.segments.size() - 1; v++)
				((RSegment) path.segments.get(v)).end.totalCount++;
		}
	}

	/**
	 * Dirties the paths that are on the given vertex
	 * 
	 * @param vertex
	 *            the vertex that has the paths
	 */
	private boolean dirtyPathsOn(RVertex vertex) {
		List paths = vertex.paths;
		if (paths != null && paths.size() != 0) {
			for (int i = 0; i < paths.size(); i++)
				((RPath) paths.get(i)).isDirty = true;
			return true;
		}
		return false;
	}

	/**
	 * Resyncs the parent paths with any new child paths that are necessary
	 * because bendpoints have been added to the parent path.
	 * 
	 * private void generateChildPaths() { for (int i = 0; i < userPaths.size();
	 * i++) { Path path = (Path)userPaths.get(i); PointList bendPoints =
	 * path.bendpoints; if (bendPoints != null && bendPoints.size() != 0) { List
	 * childPaths = new ArrayList(bendPoints.size() + 1); Path child = null;
	 * Vertex prevVertex = path.start; Vertex currVertex = null;
	 * 
	 * for (int b = 0; b < bendPoints.size(); b++) { Point bp =
	 * (Point)bendPoints.getPoint(b); currVertex = new Vertex(bp, null); child =
	 * new Path(prevVertex, currVertex); childPaths.add(child);
	 * workingPaths.add(child); prevVertex = currVertex; }
	 * 
	 * child = new Path(prevVertex, path.end); childPaths.add(child);
	 * workingPaths.add(child); pathsToChildPaths.put(path, childPaths); } else
	 * workingPaths.add(path); } //End FOR }
	 */

	/**
	 * Returns the closest vertex to the given segment.
	 * 
	 * @param v1
	 *            the first vertex
	 * @param v2
	 *            the second vertex
	 * @param segment
	 *            the segment
	 * @return v1, or v2 whichever is closest to the segment
	 */
	private RVertex getNearestVertex(RVertex v1, RVertex v2, RSegment segment) {
		if (segment.start.getDistance(v1) + segment.end.getDistance(v1) > segment.start
				.getDistance(v2) + segment.end.getDistance(v2))
			return v2;
		else
			return v1;
	}

	/**
	 * Returns the spacing maintained between paths.
	 * 
	 * @return the default path spacing
	 * @see #setSpacing(int)
	 * @since 3.2
	 */
	public int getSpacing() {
		return spacing;
	}

	/**
	 * Returns the subpath for a split on the given path at the given segment.
	 * 
	 * @param path
	 *            the path
	 * @param segment
	 *            the segment
	 * @return the new subpath
	 */
	private RPath getSubpathForSplit(RPath path, RSegment segment) {
		RPath newPath = path.getSubPath(segment);
		workingPaths.add(newPath);
		subPaths.add(newPath);
		return newPath;
	}

	/**
	 * Grows all obstacles in in routing and tests for new intersections
	 */
	private void growObstacles() {
		growPassChangedObstacles = false;
		for (int i = 0; i < NUM_GROW_PASSES; i++) {
			if (i == 0 || growPassChangedObstacles)
				growObstaclesPass();
		}
	}

	/**
	 * Performs a single pass of the grow obstacles step, this can be repeated
	 * as desired. Grows obstacles, then tests paths against the grown
	 * obstacles.
	 */
	private void growObstaclesPass() {
		// grow obstacles
		for (int i = 0; i < userObstacles.size(); i++)
			((RObstacle) userObstacles.get(i)).growVertices();

		// go through paths and test segments
		for (int i = 0; i < workingPaths.size(); i++) {
			RPath path = (RPath) workingPaths.get(i);

			for (int e = 0; e < path.excludedObstacles.size(); e++)
				((RObstacle) path.excludedObstacles.get(e)).exclude = true;

			if (path.grownSegments.size() == 0) {
				for (int s = 0; s < path.segments.size(); s++)
					testOffsetSegmentForIntersections(
							(RSegment) path.segments.get(s), -1, path);
			} else {
				int counter = 0;
				List currentSegments = new ArrayList(path.grownSegments);
				for (int s = 0; s < currentSegments.size(); s++)
					counter += testOffsetSegmentForIntersections(
							(RSegment) currentSegments.get(s), s + counter, path);
			}

			for (int e = 0; e < path.excludedObstacles.size(); e++)
				((RObstacle) path.excludedObstacles.get(e)).exclude = false;

		}

		// revert obstacles
		for (int i = 0; i < userObstacles.size(); i++)
			((RObstacle) userObstacles.get(i)).shrinkVertices();
	}

	/**
	 * Adds an obstacle to the routing
	 * 
	 * @param obs
	 *            the obstacle
	 */
	private boolean internalAddObstacle(RObstacle obs) {
		userObstacles.add(obs);
		return testAndDirtyPaths(obs);
	}

	/**
	 * Removes an obstacle from the routing.
	 * 
	 * @param rect
	 *            the bounds of the obstacle
	 * @return the obstacle removed
	 */
	private boolean internalRemoveObstacle(RRectangle rect) {
		RObstacle obs = null;
		int index = -1;
		for (int i = 0; i < userObstacles.size(); i++) {
			obs = (RObstacle) userObstacles.get(i);
			if (obs.equals(rect)) {
				index = i;
				break;
			}
		}

		userObstacles.remove(index);

		boolean result = false;
		result |= dirtyPathsOn(obs.bottomLeft);
		result |= dirtyPathsOn(obs.topLeft);
		result |= dirtyPathsOn(obs.bottomRight);
		result |= dirtyPathsOn(obs.topRight);

		for (int p = 0; p < workingPaths.size(); p++) {
			RPath path = (RPath) workingPaths.get(p);
			if (path.isDirty)
				continue;
			if (path.isObstacleVisible(obs))
				path.isDirty = result = true;
		}

		return result;
	}

	/**
	 * Labels the given path's vertices as innies, or outies, as well as
	 * determining if this path is inverted.
	 * 
	 * @param path
	 *            the path
	 */
	private void labelPath(RPath path) {
		RSegment segment = null;
		RSegment nextSegment = null;
		RVertex vertex = null;
		boolean agree = false;
		for (int v = 0; v < path.grownSegments.size() - 1; v++) {
			segment = (RSegment) path.grownSegments.get(v);
			nextSegment = (RSegment) path.grownSegments.get(v + 1);
			vertex = segment.end;
			long crossProduct = segment.crossProduct(new RSegment(vertex,
					vertex.obs.center));

			if (vertex.type == RVertex.NOT_SET) {
				labelVertex(segment, crossProduct, path);
			} else if (!path.isInverted
					&& ((crossProduct > 0 && vertex.type == RVertex.OUTIE) || (crossProduct < 0 && vertex.type == RVertex.INNIE))) {
				if (agree) {
					// split detected.
					stack.push(getSubpathForSplit(path, segment));
					return;
				} else {
					path.isInverted = true;
					path.invertPriorVertices(segment);
				}
			} else if (path.isInverted
					&& ((crossProduct < 0 && vertex.type == RVertex.OUTIE) || (crossProduct > 0 && vertex.type == RVertex.INNIE))) {
				// split detected.
				stack.push(getSubpathForSplit(path, segment));
				return;
			} else
				agree = true;

			if (vertex.paths != null) {
				for (int i = 0; i < vertex.paths.size(); i++) {
					RPath nextPath = (RPath) vertex.paths.get(i);
					if (!nextPath.isMarked) {
						nextPath.isMarked = true;
						stack.push(nextPath);
					}
				}
			}

			vertex.addPath(path, segment, nextSegment);
		}
	}

	/**
	 * Labels all path's vertices in the routing.
	 */
	private void labelPaths() {
		RPath path = null;
		for (int i = 0; i < workingPaths.size(); i++) {
			path = (RPath) workingPaths.get(i);
			stack.push(path);
		}

		while (!stack.isEmpty()) {
			path = stack.pop();
			if (!path.isMarked) {
				path.isMarked = true;
				labelPath(path);
			}
		}

		// revert is marked so we can use it again in ordering.
		for (int i = 0; i < workingPaths.size(); i++) {
			path = (RPath) workingPaths.get(i);
			path.isMarked = false;
		}
	}

	/**
	 * Labels the vertex at the end of the semgent based on the cross product.
	 * 
	 * @param segment
	 *            the segment to this vertex
	 * @param crossProduct
	 *            the cross product of this segment and a segment to the
	 *            obstacles center
	 * @param path
	 *            the path
	 */
	private void labelVertex(RSegment segment, long crossProduct, RPath path) {
		// assumes vertex in question is segment.end
		if (crossProduct > 0) {
			if (path.isInverted)
				segment.end.type = RVertex.OUTIE;
			else
				segment.end.type = RVertex.INNIE;
		} else if (crossProduct < 0) {
			if (path.isInverted)
				segment.end.type = RVertex.INNIE;
			else
				segment.end.type = RVertex.OUTIE;
		} else if (segment.start.type != RVertex.NOT_SET)
			segment.end.type = segment.start.type;
		else
			segment.end.type = RVertex.INNIE;
	}

	/**
	 * Orders the path by comparing its angle at shared vertices with other
	 * paths.
	 * 
	 * @param path
	 *            the path
	 */
	private void orderPath(RPath path) {
		if (path.isMarked)
			return;
		path.isMarked = true;
		RSegment segment = null;
		RVertex vertex = null;
		for (int v = 0; v < path.grownSegments.size() - 1; v++) {
			segment = (RSegment) path.grownSegments.get(v);
			vertex = segment.end;
			double thisAngle = ((Double) vertex.cachedCosines.get(path))
					.doubleValue();
			if (path.isInverted)
				thisAngle = -thisAngle;

			for (int i = 0; i < vertex.paths.size(); i++) {
				RPath vPath = (RPath) vertex.paths.get(i);
				if (!vPath.isMarked) {
					double otherAngle = ((Double) vertex.cachedCosines
							.get(vPath)).doubleValue();

					if (vPath.isInverted)
						otherAngle = -otherAngle;

					if (otherAngle < thisAngle)
						orderPath(vPath);
				}
			}
		}

		orderedPaths.add(path);
	}

	/**
	 * Orders all paths in the graph.
	 */
	private void orderPaths() {
		for (int i = 0; i < workingPaths.size(); i++) {
			RPath path = (RPath) workingPaths.get(i);
			orderPath(path);
		}
	}

	/**
	 * Populates the parent paths with all the child paths that were created to
	 * represent bendpoints.
	 */
	private void recombineChildrenPaths() {
		// only populate those paths with children paths.
		Iterator keyItr = pathsToChildPaths.keySet().iterator();
		while (keyItr.hasNext()) {
			RPath path = (RPath) keyItr.next();

			path.fullReset();

			List childPaths = (List) pathsToChildPaths.get(path);
			RPath childPath = null;

			for (int i = 0; i < childPaths.size(); i++) {
				childPath = (RPath) childPaths.get(i);
				path.points.addAll(childPath.getPoints());
				// path will overlap
				path.points.removePoint(path.points.size() - 1);
				// path.grownSegments.addAll(childPath.grownSegments);
				path.segments.addAll(childPath.segments);
				path.visibleObstacles.addAll(childPath.visibleObstacles);
			}

			// add last point.
			path.points.addPoint(childPath.points.getLastPoint());
		}
	}

	/**
	 * Reconnects all subpaths.
	 */
	private void recombineSubpaths() {
		for (int p = 0; p < orderedPaths.size(); p++) {
			RPath path = (RPath) orderedPaths.get(p);
			path.reconnectSubPaths();
		}

		orderedPaths.removeAll(subPaths);
		workingPaths.removeAll(subPaths);
		subPaths = null;
	}

	/**
	 * Removes the obstacle with the rectangle's bounds from the routing.
	 * 
	 * @param rect
	 *            the bounds of the obstacle to remove
	 * @return <code>true</code> if the removal has dirtied one or more paths
	 */
	public boolean removeObstacle(RRectangle rect) {
		return internalRemoveObstacle(rect);
	}

	/**
	 * Removes the given path from the routing.
	 * 
	 * @param path
	 *            the path to remove.
	 * @return <code>true</code> if the removal may have affected one of the
	 *         remaining paths
	 */
	public boolean removePath(RPath path) {
		userPaths.remove(path);
		List children = (List) pathsToChildPaths.get(path);
		if (children == null)
			workingPaths.remove(path);
		else
			workingPaths.removeAll(children);
		return true;
	}

	/**
	 * Resets exclude field on all obstacles
	 */
	private void resetObstacleExclusions() {
		for (int i = 0; i < userObstacles.size(); i++)
			((RObstacle) userObstacles.get(i)).exclude = false;
	}

	/**
	 * Resets all vertices found on paths and obstacles.
	 */
	private void resetVertices() {
		for (int i = 0; i < userObstacles.size(); i++) {
			RObstacle obs = (RObstacle) userObstacles.get(i);
			obs.reset();
		}
		for (int i = 0; i < workingPaths.size(); i++) {
			RPath path = (RPath) workingPaths.get(i);
			path.start.fullReset();
			path.end.fullReset();
		}
	}

	/**
	 * Sets the default spacing between paths. The spacing is the minimum
	 * distance that path should be offset from other paths or obstacles. The
	 * default value is 4. When this value can not be satisfied, paths will be
	 * squeezed together uniformly.
	 * 
	 * @param spacing
	 *            the path spacing
	 * @since 3.2
	 */
	public void setSpacing(int spacing) {
		this.spacing = spacing;
	}

	/**
	 * Updates the points in the paths in order to represent the current
	 * solution with the given paths and obstacles.
	 * 
	 * @return returns the list of paths which were updated.
	 */
	public List solve() {

		solveDirtyPaths();

		countVertices();
		checkVertexIntersections();
		growObstacles();

		subPaths = new ArrayList();
		stack = new PathStack();
		labelPaths();
		stack = null;

		orderedPaths = new ArrayList();
		orderPaths();
		bendPaths();

		recombineSubpaths();
		orderedPaths = null;
		subPaths = null;

		recombineChildrenPaths();
		cleanup();

		return Collections.unmodifiableList(userPaths);
	}

	/**
	 * Solves paths that are dirty.
	 * 
	 * @return number of dirty paths
	 */
	private int solveDirtyPaths() {
		int numSolved = 0;

		for (int i = 0; i < userPaths.size(); i++) {
			RPath path = (RPath) userPaths.get(i);
			if (!path.isDirty)
				continue;
			List children = (List) pathsToChildPaths.get(path);
			int prevCount = 1, newCount = 1;
			if (children == null)
				children = Collections.EMPTY_LIST;
			else
				prevCount = children.size();

			if (path.getBendPoints() != null)
				newCount = path.getBendPoints().size() + 1;

			if (prevCount != newCount)
				children = regenerateChildPaths(path, children, prevCount,
						newCount);
			refreshChildrenEndpoints(path, children);
		}

		for (int i = 0; i < workingPaths.size(); i++) {
			RPath path = (RPath) workingPaths.get(i);
			path.refreshExcludedObstacles(userObstacles);
			if (!path.isDirty) {
				path.resetPartial();
				continue;
			}

			numSolved++;
			path.fullReset();

			boolean pathFoundCheck = path.generateShortestPath(userObstacles);
			if (!pathFoundCheck || path.end.cost > path.threshold) {
				// path not found, or path found was too long
				resetVertices();
				path.fullReset();
				path.threshold = 0;
				pathFoundCheck = path.generateShortestPath(userObstacles);
			}

			resetVertices();
		}

		resetObstacleExclusions();

		if (numSolved == 0)
			resetVertices();

		return numSolved;
	}

	/**
	 * @since 3.0
	 * @param path
	 * @param children
	 */
	private void refreshChildrenEndpoints(RPath path, List children) {
		RPoint previous = path.getStartPoint();
		RPoint next;
		RPointList bendpoints = path.getBendPoints();
		RPath child;

		for (int i = 0; i < children.size(); i++) {
			if (i < bendpoints.size())
				next = bendpoints.getPoint(i);
			else
				next = path.getEndPoint();
			child = (RPath) children.get(i);
			child.setStartPoint(previous);
			child.setEndPoint(next);
			previous = next;
		}
	}

	/**
	 * @since 3.0
	 * @param path
	 * @param children
	 */
	private List regenerateChildPaths(RPath path, List children,
			int currentSize, int newSize) {
		// Path used to be simple but now is compound, children is EMPTY.
		if (currentSize == 1) {
			workingPaths.remove(path);
			currentSize = 0;
			children = new ArrayList(newSize);
			pathsToChildPaths.put(path, children);
		} else
		// Path is becoming simple but was compound. children becomes empty.
		if (newSize == 1) {
			workingPaths.removeAll(children);
			workingPaths.add(path);
			pathsToChildPaths.remove(path);
			return Collections.EMPTY_LIST;
		}

		// Add new working paths until the sizes are the same
		while (currentSize < newSize) {
			RPath child = new RPath();
			workingPaths.add(child);
			children.add(child);
			currentSize++;
		}

		while (currentSize > newSize) {
			RPath child = (RPath) children.remove(children.size() - 1);
			workingPaths.remove(child);
			currentSize--;
		}

		return children;
	}

	/**
	 * Tests a segment that has been offset for new intersections
	 * 
	 * @param segment
	 *            the segment
	 * @param index
	 *            the index of the segment along the path
	 * @param path
	 *            the path
	 * @return 1 if new segments have been inserted
	 */
	private int testOffsetSegmentForIntersections(RSegment segment, int index,
			RPath path) {
		for (int i = 0; i < userObstacles.size(); i++) {
			RObstacle obs = (RObstacle) userObstacles.get(i);

			if (segment.end.obs == obs || segment.start.obs == obs
					|| obs.exclude)
				continue;
			RVertex vertex = null;

			int offset = getSpacing();
			if (segment.getSlope() < 0) {
				if (segment.intersects(obs.topLeft.x - offset, obs.topLeft.y
						- offset, obs.bottomRight.x + offset, obs.bottomRight.y
						+ offset))
					vertex = getNearestVertex(obs.topLeft, obs.bottomRight,
							segment);
				else if (segment.intersects(obs.bottomLeft.x - offset,
						obs.bottomLeft.y + offset, obs.topRight.x + offset,
						obs.topRight.y - offset))
					vertex = getNearestVertex(obs.bottomLeft, obs.topRight,
							segment);
			} else {
				if (segment.intersects(obs.bottomLeft.x - offset,
						obs.bottomLeft.y + offset, obs.topRight.x + offset,
						obs.topRight.y - offset))
					vertex = getNearestVertex(obs.bottomLeft, obs.topRight,
							segment);
				else if (segment.intersects(obs.topLeft.x - offset,
						obs.topLeft.y - offset, obs.bottomRight.x + offset,
						obs.bottomRight.y + offset))
					vertex = getNearestVertex(obs.topLeft, obs.bottomRight,
							segment);
			}

			if (vertex != null) {
				RRectangle vRect = vertex.getDeformedRectangle(offset);
				if (segment.end.obs != null) {
					RRectangle endRect = segment.end
							.getDeformedRectangle(offset);
					if (vRect.intersects(endRect))
						continue;
				}
				if (segment.start.obs != null) {
					RRectangle startRect = segment.start
							.getDeformedRectangle(offset);
					if (vRect.intersects(startRect))
						continue;
				}

				RSegment newSegmentStart = new RSegment(segment.start, vertex);
				RSegment newSegmentEnd = new RSegment(vertex, segment.end);

				vertex.totalCount++;
				vertex.nearestObstacleChecked = false;

				vertex.shrink();
				checkVertexForIntersections(vertex);
				vertex.grow();

				if (vertex.nearestObstacle != 0)
					vertex.updateOffset();

				growPassChangedObstacles = true;

				if (index != -1) {
					path.grownSegments.remove(segment);
					path.grownSegments.add(index, newSegmentStart);
					path.grownSegments.add(index + 1, newSegmentEnd);
				} else {
					path.grownSegments.add(newSegmentStart);
					path.grownSegments.add(newSegmentEnd);
				}
				return 1;
			}
		}
		if (index == -1)
			path.grownSegments.add(segment);
		return 0;
	}

	/**
	 * Tests all paths against the given obstacle
	 * 
	 * @param obs
	 *            the obstacle
	 */
	private boolean testAndDirtyPaths(RObstacle obs) {
		boolean result = false;
		for (int i = 0; i < workingPaths.size(); i++) {
			RPath path = (RPath) workingPaths.get(i);
			result |= path.testAndSet(obs);
		}
		return result;
	}

	/**
	 * Updates the position of an existing obstacle.
	 * 
	 * @param oldBounds
	 *            the old bounds(used to find the obstacle)
	 * @param newBounds
	 *            the new bounds
	 * @return <code>true</code> if the change the current results to become
	 *         stale
	 */
	public boolean updateObstacle(RRectangle oldBounds, RRectangle newBounds) {
		boolean result = internalRemoveObstacle(oldBounds);
		result |= addObstacle(newBounds);
		return result;
	}

}
