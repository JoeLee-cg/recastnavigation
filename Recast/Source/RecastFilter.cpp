//
// Copyright (c) 2009-2010 Mikko Mononen memon@inside.org
//
// This software is provided 'as-is', without any express or implied
// warranty.  In no event will the authors be held liable for any damages
// arising from the use of this software.
// Permission is granted to anyone to use this software for any purpose,
// including commercial applications, and to alter it and redistribute it
// freely, subject to the following restrictions:
// 1. The origin of this software must not be misrepresented; you must not
//    claim that you wrote the original software. If you use this software
//    in a product, an acknowledgment in the product documentation would be
//    appreciated but is not required.
// 2. Altered source versions must be plainly marked as such, and must not be
//    misrepresented as being the original software.
// 3. This notice may not be removed or altered from any source distribution.
//

#include "Recast.h"
#include "RecastAssert.h"

#include <stdlib.h>

void rcFilterLowHangingWalkableObstacles(rcContext* context, const int walkableClimb, rcHeightfield& heightfield)
{
	rcAssert(context);

	rcScopedTimer timer(context, RC_TIMER_FILTER_LOW_OBSTACLES);

	const int xSize = heightfield.width;
	const int zSize = heightfield.height;

	// 遍历高度场格子
	for (int z = 0; z < zSize; ++z)
	{
		for (int x = 0; x < xSize; ++x)
		{
			// 记录上一个 span 的信息
			rcSpan* previousSpan = NULL;
			bool previousWasWalkable = false;
			unsigned char previousArea = RC_NULL_AREA;

			for (rcSpan* span = heightfield.spans[x + z * xSize]; span != NULL; previousSpan = span, span = span->next)
			{
				// span 是否可走
				const bool walkable = span->area != RC_NULL_AREA;
				// If current span is not walkable, but there is walkable
				// span just below it, mark the span above it walkable too.
				if (!walkable && previousWasWalkable)
				{
					// 如果当前 span 是不可走而 上一个 span是可走的
					if (rcAbs((int)span->smax - (int)previousSpan->smax) <= walkableClimb)
					{
						// 如果当前 span 和上一个 span的高度差小于等于 walkableClimb，则把 span 场地 ID 标记为上一个 span 同一场地 ID
						span->area = previousArea;
					}
				}
				// Copy walkable flag so that it cannot propagate
				// past multiple non-walkable objects.
				// 更新上一个 span 的信息（todo: walkable需要更新？）
				previousWasWalkable = walkable;
				previousArea = span->area;
			}
		}
	}
}

void rcFilterLedgeSpans(rcContext* context, const int walkableHeight, const int walkableClimb,
                        rcHeightfield& heightfield)
{
	rcAssert(context);
	
	rcScopedTimer timer(context, RC_TIMER_FILTER_BORDER);

	const int xSize = heightfield.width;
	const int zSize = heightfield.height;
	const int MAX_HEIGHT = 0xffff; // TODO (graham): Move this to a more visible constant and update usages.
	
	// Mark border spans.
	for (int z = 0; z < zSize; ++z)
	{
		for (int x = 0; x < xSize; ++x)
		{
			for (rcSpan* span = heightfield.spans[x + z * xSize]; span; span = span->next)
			{
				// Skip non walkable spans.
				// 跳过不可行走的 span
				if (span->area == RC_NULL_AREA)
				{
					continue;
				}

				// 两个 span 之间的间隙
				const int bot = (int)(span->smax);
				const int top = span->next ? (int)(span->next->smin) : MAX_HEIGHT;

				// Find neighbours minimum height.
				// 最小高度差
				int minNeighborHeight = MAX_HEIGHT;

				// Min and max height of accessible neighbours.
				// 相邻格子的最小可行走高度
				int accessibleNeighborMinHeight = span->smax;
				// 相邻格子的最大可行走高度
				int accessibleNeighborMaxHeight = span->smax;

				// 遍历相邻四个方向的 span
				// 对于 bot 大于 0 的情况，其实 -walkableClimb - bot 这个高度差已经满足 minNeighborHeight > - walkableClimb 了，可以直接 break 了
				// 对于 bot 小于等于 0 的情况，当前 span 还是可能会避免标记为不可走
				// bot 小于等于0，是导航的第一层
				for (int direction = 0; direction < 4; ++direction)
				{
					int dx = x + rcGetDirOffsetX(direction);
					int dy = z + rcGetDirOffsetY(direction);
					// Skip neighbours which are out of bounds.
					if (dx < 0 || dy < 0 || dx >= xSize || dy >= zSize)
					{
						// 如果超过高度域范围，把 minNeighborHeight 标记为 -walkableClimb - bot，跳过
						minNeighborHeight = rcMin(minNeighborHeight, -walkableClimb - bot);
						continue;
					}

					// From minus infinity to the first span.
					const rcSpan* neighborSpan = heightfield.spans[dx + dy * xSize];
					int neighborBot = -walkableClimb;
					int neighborTop = neighborSpan ? (int)neighborSpan->smin : MAX_HEIGHT;
					
					// Skip neighbour if the gap between the spans is too small.
					if (rcMin(top, neighborTop) - rcMax(bot, neighborBot) > walkableHeight)
					{
						// 如果相邻初始 span 的底部与当前 span 的行走面相差超过 walkableHeight，则跳过
						// 其实这里是不是少了个 continue ？因为下面的遍历已经没有意义了
						minNeighborHeight = rcMin(minNeighborHeight, neighborBot - bot);
					}

					// Rest of the spans.
					// 遍历相邻格子的 span 链表
					for (neighborSpan = heightfield.spans[dx + dy * xSize]; neighborSpan; neighborSpan = neighborSpan->next)
					{
						// 相邻格子上下两个 span 的间隙
						neighborBot = (int)neighborSpan->smax;
						neighborTop = neighborSpan->next ? (int)neighborSpan->next->smin : MAX_HEIGHT;
						
						// Skip neighbour if the gap between the spans is too small.
						if (rcMin(top, neighborTop) - rcMax(bot, neighborBot) > walkableHeight)
						{
							// 如果这两个间隙连通（空间高度差小于 walkableHeight）
							// 获取这两个 span 的行走面的最小高度差
							minNeighborHeight = rcMin(minNeighborHeight, neighborBot - bot);

							// Find min/max accessible neighbour height. 
							if (rcAbs(neighborBot - bot) <= walkableClimb)
							{
								// 如果两个 span 的行走面的高度差小于 walkableClimb，获取相邻格子可行走表面的最小和最大高度
								if (neighborBot < accessibleNeighborMinHeight) accessibleNeighborMinHeight = neighborBot;
								if (neighborBot > accessibleNeighborMaxHeight) accessibleNeighborMaxHeight = neighborBot;
							}

						}
					}
				}

				// The current span is close to a ledge if the drop to any
				// neighbour span is less than the walkableClimb.
				if (minNeighborHeight < -walkableClimb)
				{
					// 如果相邻格子与当前 span 的高度差大于 walkableClimb，则 span 当作是突起，不可走
					span->area = RC_NULL_AREA;
				}
				// If the difference between all neighbours is too large,
				// we are at steep slope, mark the span as ledge.
				else if ((accessibleNeighborMaxHeight - accessibleNeighborMinHeight) > walkableClimb)
				{
					// 如果各个 span 的可行走表面高度差超过 walkableClimb，则 span 当作是突起，不可走 
					span->area = RC_NULL_AREA;
				}
			}
		}
	}
}

void rcFilterWalkableLowHeightSpans(rcContext* context, const int walkableHeight, rcHeightfield& heightfield)
{
	rcAssert(context);
	
	rcScopedTimer timer(context, RC_TIMER_FILTER_WALKABLE);
	
	const int xSize = heightfield.width;
	const int zSize = heightfield.height;
	const int MAX_HEIGHT = 0xffff;
	
	// Remove walkable flag from spans which do not have enough
	// space above them for the agent to stand there.
	for (int z = 0; z < zSize; ++z)
	{
		for (int x = 0; x < xSize; ++x)
		{
			for (rcSpan* span = heightfield.spans[x + z*xSize]; span; span = span->next)
			{
				const int bot = (int)(span->smax);
				const int top = span->next ? (int)(span->next->smin) : MAX_HEIGHT;
				if ((top - bot) < walkableHeight)
				{
					span->area = RC_NULL_AREA;
				}
			}
		}
	}
}
