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

#include <float.h>
#include <math.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include "Recast.h"
#include "RecastAlloc.h"
#include "RecastAssert.h"


// Must be 255 or smaller (not 256) because layer IDs are stored as
// a byte where 255 is a special value.
#ifndef RC_MAX_LAYERS_DEF
#define RC_MAX_LAYERS_DEF 63
#endif

#if RC_MAX_LAYERS_DEF > 255
#error RC_MAX_LAYERS_DEF must be 255 or smaller
#endif

#ifndef RC_MAX_NEIS_DEF
#define RC_MAX_NEIS_DEF 16
#endif

// Keep type checking.
static const int RC_MAX_LAYERS = RC_MAX_LAYERS_DEF;
static const int RC_MAX_NEIS = RC_MAX_NEIS_DEF;

struct rcLayerRegion
{
	unsigned char layers[RC_MAX_LAYERS];
	unsigned char neis[RC_MAX_NEIS];
	unsigned short ymin, ymax;
	unsigned char layerId;		// Layer ID
	unsigned char nlayers;		// Layer count
	unsigned char nneis;		// Neighbour count
	unsigned char base;		// Flag indicating if the region is the base of merged regions.
};


static bool contains(const unsigned char* a, const unsigned char an, const unsigned char v)
{
	const int n = (int)an;
	for (int i = 0; i < n; ++i)
	{
		if (a[i] == v)
			return true;
	}
	return false;
}

static bool addUnique(unsigned char* a, unsigned char& an, int anMax, unsigned char v)
{
	if (contains(a, an, v))
		return true;

	if ((int)an >= anMax)
		return false;

	a[an] = v;
	an++;
	return true;
}


inline bool overlapRange(const unsigned short amin, const unsigned short amax,
						 const unsigned short bmin, const unsigned short bmax)
{
	return (amin > bmax || amax < bmin) ? false : true;
}



struct rcLayerSweepSpan
{
	unsigned short ns;	// number samples
	unsigned char id;	// region id
	unsigned char nei;	// neighbour id
};

/// @par
/// 
/// See the #rcConfig documentation for more information on the configuration parameters.
/// 
/// @see rcAllocHeightfieldLayerSet, rcCompactHeightfield, rcHeightfieldLayerSet, rcConfig
bool rcBuildHeightfieldLayers(rcContext* ctx, const rcCompactHeightfield& chf,
							  const int borderSize, const int walkableHeight,
							  rcHeightfieldLayerSet& lset)
{
	rcAssert(ctx);
	
	rcScopedTimer timer(ctx, RC_TIMER_BUILD_LAYERS);
	
	const int w = chf.width;
	const int h = chf.height;
	
	// 创建每一个 span 对应的区域 ID 数据区
	rcScopedDelete<unsigned char> srcReg((unsigned char*)rcAlloc(sizeof(unsigned char)*chf.spanCount, RC_ALLOC_TEMP));
	if (!srcReg)
	{
		ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: Out of memory 'srcReg' (%d).", chf.spanCount);
		return false;
	}
	// 初始化区域 ID 为 0xff
	memset(srcReg,0xff,sizeof(unsigned char)*chf.spanCount);
	
	// 创建 sweep 数据区， 每一行为一组 sweep ，逐行扫描
	// 每一个 sweep 可以看作是这一行的一个区域
	const int nsweeps = chf.width;
	rcScopedDelete<rcLayerSweepSpan> sweeps((rcLayerSweepSpan*)rcAlloc(sizeof(rcLayerSweepSpan)*nsweeps, RC_ALLOC_TEMP));
	if (!sweeps)
	{
		ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: Out of memory 'sweeps' (%d).", nsweeps);
		return false;
	}
	
	
	// Partition walkable area into monotone regions.
	// prevCount 是每个区域与其它区域相连的 span 的数量
	int prevCount[256];
	// 区域 ID 从 0 开始
	unsigned char regId = 0;

	// 从左下角开始遍历 span ，剔除 四边的 border
	for (int y = borderSize; y < h-borderSize; ++y)
	{
		memset(prevCount,0,sizeof(int)*regId);
		unsigned char sweepId = 0;
		
		for (int x = borderSize; x < w-borderSize; ++x)
		{
			const rcCompactCell& c = chf.cells[x+y*w];
			
			// 遍历当前格子的 span
			for (int i = (int)c.index, ni = (int)(c.index+c.count); i < ni; ++i)
			{
				const rcCompactSpan& s = chf.spans[i];

				// 不可走区域，跳过
				if (chf.areas[i] == RC_NULL_AREA) continue;

				// 初始化区域 ID 为 0xff
				unsigned char sid = 0xff;

				// -x
				// 如果左边存在相连 span
				if (rcGetCon(s, 0) != RC_NOT_CONNECTED)
				{
					const int ax = x + rcGetDirOffsetX(0);
					const int ay = y + rcGetDirOffsetY(0);
					const int ai = (int)chf.cells[ax+ay*w].index + rcGetCon(s, 0);

					// 如果左边 span 可走并且其区域 ID 已赋值，则把当前 span 与其设为同一区域 ID
					if (chf.areas[ai] != RC_NULL_AREA && srcReg[ai] != 0xff)
						sid = srcReg[ai];
				}
				
				// 如果 sid 还未初始化
				if (sid == 0xff)
				{
					// 用本行 sweep id 作为其区域 ID
					sid = sweepId++;
					// 相邻区域 ID
					sweeps[sid].nei = 0xff;
					// 与相邻区域连接的 span 数量
					sweeps[sid].ns = 0;
				}
				
				// -y
				// 如果下方存在相连 span
				if (rcGetCon(s,3) != RC_NOT_CONNECTED)
				{
					const int ax = x + rcGetDirOffsetX(3);
					const int ay = y + rcGetDirOffsetY(3);
					const int ai = (int)chf.cells[ax+ay*w].index + rcGetCon(s, 3);

					// 下方 span 区域 ID
					const unsigned char nr = srcReg[ai];
					// 如果下方 span 已有区域
					if (nr != 0xff)
					{
						// Set neighbour when first valid neighbour is encoutered.
						// 如果当前没有邻接区域，设置邻接区域 ID 为 nr
						if (sweeps[sid].ns == 0)
							sweeps[sid].nei = nr;
						
						// 如果当前邻接区域与下方 span 区域相同
						if (sweeps[sid].nei == nr)
						{
							// Update existing neighbour
							// 增加连接 span 的数量
							sweeps[sid].ns++;
							// 增加 nr 区域连接 span 数量
							prevCount[nr]++;
						}
						else
						{
							// This is hit if there is nore than one neighbour.
							// Invalidate the neighbour.
							// 如果下方邻接区域不止一个，则让其邻接区域无效
							// 这样会导致后续的 sweeps[sid].ns 和 prevCount 不会增加
							sweeps[sid].nei = 0xff;
						}
					}
				}
				// 更新 srcReg[i]
				srcReg[i] = sid;
			}
		}
		
		// Create unique ID.
		// 根据当前行的 sweep id 创建全局唯一的区域 ID
		for (int i = 0; i < sweepId; ++i)
		{
			// If the neighbour is set and there is only one continuous connection to it,
			// the sweep will be merged with the previous one, else new region is created.
			if (sweeps[i].nei != 0xff && prevCount[sweeps[i].nei] == (int)sweeps[i].ns)
			{
				// 把当前 sweep 归并到相邻区域需要满足两个条件：
				// 1、如果存在相邻区域，并且相邻区域只有一个（上面在不止一个相邻区域的时候，把 sweeps[i].nei 设成了 0xff）
				// 2、并且相邻区域连接外部区域的 span 数量等于当前 sweep 连接的 span 数量时
				// 条件1、2分别应对两种情况：
				// 1、一个长 sweep 对应下方两个短区域
				// 2、两个短 sweep 对应下方一个长区域
				sweeps[i].id = sweeps[i].nei;
			}
			else
			{
				if (regId == 255)
				{
					ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: Region ID overflow.");
					return false;
				}
				// 否则把当前 sweep 设置成一个新的区域
				sweeps[i].id = regId++;
			}
		}
		
		// Remap local sweep ids to region ids.
		// 对于本行 span ，srcReg 里还是保存着 sweep id ，需要更新为新的唯一区域 ID 
		for (int x = borderSize; x < w-borderSize; ++x)
		{
			const rcCompactCell& c = chf.cells[x+y*w];
			for (int i = (int)c.index, ni = (int)(c.index+c.count); i < ni; ++i)
			{
				// 如果当前 span 赋予了 sweep id
				if (srcReg[i] != 0xff)
					srcReg[i] = sweeps[srcReg[i]].id;
			}
		}
	}

	// Allocate and init layer regions.
	// 生成分层区域集的数据区
	const int nregs = (int)regId;
	rcScopedDelete<rcLayerRegion> regs((rcLayerRegion*)rcAlloc(sizeof(rcLayerRegion)*nregs, RC_ALLOC_TEMP));
	if (!regs)
	{
		ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: Out of memory 'regs' (%d).", nregs);
		return false;
	}
	memset(regs, 0, sizeof(rcLayerRegion)*nregs);
	// 初始化层级数据
	for (int i = 0; i < nregs; ++i)
	{
		// 层级 ID
		regs[i].layerId = 0xff;
		// 当前层级最小高度
		regs[i].ymin = 0xffff;
		// 当前层级最大高度
		regs[i].ymax = 0;
	}
	
	// Find region neighbours and overlapping regions.
	// 查找相邻区域和重叠区域
	for (int y = 0; y < h; ++y)
	{
		for (int x = 0; x < w; ++x)
		{
			const rcCompactCell& c = chf.cells[x+y*w];
			
			// 先按当前格子每一个 span 分层，缓存在 lregs
			unsigned char lregs[RC_MAX_LAYERS];
			int nlregs = 0;
			
			// 查找相邻区域
			for (int i = (int)c.index, ni = (int)(c.index+c.count); i < ni; ++i)
			{
				// 当前 span
				const rcCompactSpan& s = chf.spans[i];
				// 当前 span 的区域 ID
				const unsigned char ri = srcReg[i];
				if (ri == 0xff) continue;
				
				// 更新层级最小和最大高度
				regs[ri].ymin = rcMin(regs[ri].ymin, s.y);
				regs[ri].ymax = rcMax(regs[ri].ymax, s.y);
				
				// Collect all region layers.
				// 缓存当前层的区域 ID
				if (nlregs < RC_MAX_LAYERS)
					lregs[nlregs++] = ri;
				
				// Update neighbours
				// 更新相邻 span
				for (int dir = 0; dir < 4; ++dir)
				{
					// 当前方向有连接
					if (rcGetCon(s, dir) != RC_NOT_CONNECTED)
					{
						const int ax = x + rcGetDirOffsetX(dir);
						const int ay = y + rcGetDirOffsetY(dir);
						const int ai = (int)chf.cells[ax+ay*w].index + rcGetCon(s, dir);
						// 当前方向连接的 span 的区域 ID
						const unsigned char rai = srcReg[ai];
						if (rai != 0xff && rai != ri)
						{
							// Don't check return value -- if we cannot add the neighbor
							// it will just cause a few more regions to be created, which
							// is fine.
							// 如果相邻 span 存在区域 ID 并且与当前 span 区域不相同，添加相邻区域
							addUnique(regs[ri].neis, regs[ri].nneis, RC_MAX_NEIS, rai);
						}
					}
				}
				
			}
			
			// Update overlapping regions.
			// 查找重叠区域
			for (int i = 0; i < nlregs-1; ++i)
			{
				for (int j = i+1; j < nlregs; ++j)
				{
					// i j 分别为上下两个 span 的区域 ID
					if (lregs[i] != lregs[j])
					{
						// 如果上下两个 span 的区域 ID 不一样
						rcLayerRegion& ri = regs[lregs[i]];
						rcLayerRegion& rj = regs[lregs[j]];

						// 互相添加重叠的区域 ID
						if (!addUnique(ri.layers, ri.nlayers, RC_MAX_LAYERS, lregs[j]) ||
							!addUnique(rj.layers, rj.nlayers, RC_MAX_LAYERS, lregs[i]))
						{
							ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: layer overflow (too many overlapping walkable platforms). Try increasing RC_MAX_LAYERS.");
							return false;
						}
					}
				}
			}
			
		}
	}
	
	// Create 2D layers from regions.
	// 创建区域的平面层级
	unsigned char layerId = 0;
	
	static const int MAX_STACK = 64;
	unsigned char stack[MAX_STACK];
	int nstack = 0;
	
	// 遍历每一个区域
	for (int i = 0; i < nregs; ++i)
	{
		// 根区域
		rcLayerRegion& root = regs[i];
		// Skip already visited.
		// 如果这个区域已级设置了层级，跳过
		if (root.layerId != 0xff)
			continue;

		// Start search.
		// 设置层级
		root.layerId = layerId;
		// 这是当前层级的根区域
		root.base = 1;
		
		// 入栈
		nstack = 0;
		stack[nstack++] = (unsigned char)i;
		
		// 查找同一层级的所有区域
		while (nstack)
		{
			// Pop front
			// 出栈
			rcLayerRegion& reg = regs[stack[0]];
			nstack--;
			for (int j = 0; j < nstack; ++j)
				stack[j] = stack[j+1];
			
			// 遍历相邻的区域
			const int nneis = (int)reg.nneis;
			for (int j = 0; j < nneis; ++j)
			{
				const unsigned char nei = reg.neis[j];
				// 相邻区域
				rcLayerRegion& regn = regs[nei];
				// Skip already visited.
				// 如果相邻区域已级设置了层级，跳过
				if (regn.layerId != 0xff)
					continue;
				// Skip if the neighbour is overlapping root region.
				// 如果这个区域与当前层级的所有区域有重叠，跳过
				if (contains(root.layers, root.nlayers, nei))
					continue;
				// Skip if the height range would become too large.
				const int ymin = rcMin(root.ymin, regn.ymin);
				const int ymax = rcMax(root.ymax, regn.ymax);
				// 如果把 regn 合并到当前层级之后，最小最大高度差超过255，跳过
				if ((ymax - ymin) >= 255)
					 continue;

				// 如果堆栈还没满，合并区域到当前层级
				if (nstack < MAX_STACK)
				{
					// Deepen
					// 入栈
					stack[nstack++] = (unsigned char)nei;
					
					// Mark layer id
					// 设置当前层级 ID
					regn.layerId = layerId;
					// Merge current layers to root.
					// regn 重叠的其它区域合并到当前层级的 root 区域
					for (int k = 0; k < regn.nlayers; ++k)
					{
						if (!addUnique(root.layers, root.nlayers, RC_MAX_LAYERS, regn.layers[k]))
						{
							ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: layer overflow (too many overlapping walkable platforms). Try increasing RC_MAX_LAYERS.");
							return false;
						}
					}
					// 更新层级的最小最大高度
					root.ymin = rcMin(root.ymin, regn.ymin);
					root.ymax = rcMax(root.ymax, regn.ymax);
				}
			}
		}
		
		layerId++;
	}
	
	// Merge non-overlapping regions that are close in height.
	// 合并不重叠并且相差高度小于 walkableHeight * 4 的区域
	const unsigned short mergeHeight = (unsigned short)walkableHeight * 4;
	
	for (int i = 0; i < nregs; ++i)
	{
		rcLayerRegion& ri = regs[i];
		// 如果层级的不是根区域，跳过（根区域在上面把 base 设为了 1，根区域有所有合并后的信息）
		if (!ri.base) continue;
		
		// 合并后的层级 ID
		unsigned char newId = ri.layerId;
		
		// 不断遍历其它区域，直到没找到可合并层级为止
		for (;;)
		{
			unsigned char oldId = 0xff;
			
			for (int j = 0; j < nregs; ++j)
			{
				if (i == j) continue;
				rcLayerRegion& rj = regs[j];
				if (!rj.base) continue;
				
				// Skip if the regions are not close to each other.
				// 如果两个层级的高度在范围内没有重叠，跳过
				if (!overlapRange(ri.ymin,ri.ymax+mergeHeight, rj.ymin,rj.ymax+mergeHeight))
					continue;
				// Skip if the height range would become too large.
				const int ymin = rcMin(ri.ymin, rj.ymin);
				const int ymax = rcMax(ri.ymax, rj.ymax);
				// 如果合并后层级的最小最大高度大于等于255，跳过
				if ((ymax - ymin) >= 255)
				  continue;
						  
				// Make sure that there is no overlap when merging 'ri' and 'rj'.
				bool overlap = false;
				// Iterate over all regions which have the same layerId as 'rj'
				for (int k = 0; k < nregs; ++k)
				{
					if (regs[k].layerId != rj.layerId)
						continue;
					// Check if region 'k' is overlapping region 'ri'
					// Index to 'regs' is the same as region id.
					if (contains(ri.layers,ri.nlayers, (unsigned char)k))
					{
						overlap = true;
						break;
					}
				}
				// Cannot merge of regions overlap.
				// 如果 ri 和 rj 有重叠，跳过
				if (overlap)
					continue;
				
				// Can merge i and j.
				oldId = rj.layerId;
				break;
			}
			
			// Could not find anything to merge with, stop.
			// 没找到可以合并的层级，跳出死循环
			if (oldId == 0xff)
				break;
			
			// Merge
			// 合并层级
			for (int j = 0; j < nregs; ++j)
			{
				rcLayerRegion& rj = regs[j];

				// 合并这个层级的所有区域
				if (rj.layerId == oldId)
				{
					// 清除根区域标记
					rj.base = 0;
					// Remap layerIds.
					// 设置新的层级 ID
					rj.layerId = newId;
					// Add overlaid layers from 'rj' to 'ri'.
					// 把这个区域已重叠区域的 ID 添加到根区域
					for (int k = 0; k < rj.nlayers; ++k)
					{
						if (!addUnique(ri.layers, ri.nlayers, RC_MAX_LAYERS, rj.layers[k]))
						{
							ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: layer overflow (too many overlapping walkable platforms). Try increasing RC_MAX_LAYERS.");
							return false;
						}
					}

					// Update height bounds.
					// 更新合并后层级的最小最大高度
					ri.ymin = rcMin(ri.ymin, rj.ymin);
					ri.ymax = rcMax(ri.ymax, rj.ymax);
				}
			}
		}
	}
	
	// Compact layerIds
	// 因为合并过层级，所以现在层级的 ID 不是连续的，压缩层级 ID
	unsigned char remap[256];
	memset(remap, 0, 256);

	// Find number of unique layers.
	layerId = 0;
	// 用 map 为 1 标记这个层级 ID 是已级使用的
	for (int i = 0; i < nregs; ++i)
		remap[regs[i].layerId] = 1;
	for (int i = 0; i < 256; ++i)
	{
		// 对于所有已用的层级 ID，赋予紧凑 ID
		if (remap[i])
			remap[i] = layerId++;
		else
			remap[i] = 0xff;
	}
	// Remap ids.
	// 更新紧凑 ID
	for (int i = 0; i < nregs; ++i)
		regs[i].layerId = remap[regs[i].layerId];
	
	// No layers, return empty.
	if (layerId == 0)
		return true;
	
	// Create layers.
	rcAssert(lset.layers == 0);
	
	// 剔除 border
	const int lw = w - borderSize*2;
	const int lh = h - borderSize*2;

	// Build contracted bbox for layers.
	// 包围盒去掉 border
	float bmin[3], bmax[3];
	rcVcopy(bmin, chf.bmin);
	rcVcopy(bmax, chf.bmax);
	bmin[0] += borderSize*chf.cs;
	bmin[2] += borderSize*chf.cs;
	bmax[0] -= borderSize*chf.cs;
	bmax[2] -= borderSize*chf.cs;
	
	lset.nlayers = (int)layerId;
	
	// 创建层级数据区
	lset.layers = (rcHeightfieldLayer*)rcAlloc(sizeof(rcHeightfieldLayer)*lset.nlayers, RC_ALLOC_PERM);
	if (!lset.layers)
	{
		ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: Out of memory 'layers' (%d).", lset.nlayers);
		return false;
	}
	memset(lset.layers, 0, sizeof(rcHeightfieldLayer)*lset.nlayers);

	
	// Store layers.
	for (int i = 0; i < lset.nlayers; ++i)
	{
		// 当前层级 ID
		unsigned char curId = (unsigned char)i;

		// 当前层级数据
		rcHeightfieldLayer* layer = &lset.layers[i];

		// 剔除 border 后的格子数
		const int gridSize = sizeof(unsigned char)*lw*lh;

		// 当前层级所在格子的高度数据区
		layer->heights = (unsigned char*)rcAlloc(gridSize, RC_ALLOC_PERM);
		if (!layer->heights)
		{
			ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: Out of memory 'heights' (%d).", gridSize);
			return false;
		}
		// 初始化为最大值
		memset(layer->heights, 0xff, gridSize);

		// 当前层级所在格子的场地 ID 数据区
		layer->areas = (unsigned char*)rcAlloc(gridSize, RC_ALLOC_PERM);
		if (!layer->areas)
		{
			ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: Out of memory 'areas' (%d).", gridSize);
			return false;
		}
		memset(layer->areas, 0, gridSize);

		// 当前层级所在格子的连接数据区
		layer->cons = (unsigned char*)rcAlloc(gridSize, RC_ALLOC_PERM);
		if (!layer->cons)
		{
			ctx->log(RC_LOG_ERROR, "rcBuildHeightfieldLayers: Out of memory 'cons' (%d).", gridSize);
			return false;
		}
		memset(layer->cons, 0, gridSize);
		
		// 获取层级的高度范围
		// Find layer height bounds.
		int hmin = 0, hmax = 0;
		for (int j = 0; j < nregs; ++j)
		{
			if (regs[j].base && regs[j].layerId == curId)
			{
				hmin = (int)regs[j].ymin;
				hmax = (int)regs[j].ymax;
			}
		}

		// 层级宽度
		layer->width = lw;
		// 层级长度
		layer->height = lh;
		// 格子边长
		layer->cs = chf.cs;
		// 格子高度
		layer->ch = chf.ch;
		
		// Adjust the bbox to fit the heightfield.
		rcVcopy(layer->bmin, bmin);
		rcVcopy(layer->bmax, bmax);
		layer->bmin[1] = bmin[1] + hmin*chf.ch;
		layer->bmax[1] = bmin[1] + hmax*chf.ch;
		layer->hmin = hmin;
		layer->hmax = hmax;

		// Update usable data region.
		layer->minx = layer->width;
		layer->maxx = 0;
		layer->miny = layer->height;
		layer->maxy = 0;
		
		// Copy height and area from compact heightfield. 
		for (int y = 0; y < lh; ++y)
		{
			for (int x = 0; x < lw; ++x)
			{
				const int cx = borderSize+x;
				const int cy = borderSize+y;
				const rcCompactCell& c = chf.cells[cx+cy*w];
				for (int j = (int)c.index, nj = (int)(c.index+c.count); j < nj; ++j)
				{
					// 当前 span
					const rcCompactSpan& s = chf.spans[j];
					// Skip unassigned regions.
					// 如果当前 span 区域 ID 无效，跳过
					if (srcReg[j] == 0xff)
						continue;
					// Skip of does nto belong to current layer.
					// 当前 span 层级 ID
					unsigned char lid = regs[srcReg[j]].layerId;
					// 非当前层级的 span ，跳过
					if (lid != curId)
						continue;
					
					// Update data bounds.
					// 把当前 span 添加到层级包围盒
					layer->minx = rcMin(layer->minx, x);
					layer->maxx = rcMax(layer->maxx, x);
					layer->miny = rcMin(layer->miny, y);
					layer->maxy = rcMax(layer->maxy, y);
					
					// Store height and area type.
					const int idx = x+y*lw;
					// 设置当前层级所在格子的高度
					layer->heights[idx] = (unsigned char)(s.y - hmin);
					// 设置当前层级所在格子的场地 ID
					layer->areas[idx] = chf.areas[j];
					
					// Check connection.
					// 更新当前层级所在格子的连接
					// 外部连接，连接其它 layer
					unsigned char portal = 0;
					// 内部连接，连接其它格子
					unsigned char con = 0;
					for (int dir = 0; dir < 4; ++dir)
					{
						// 如果当前方向上 span 有连接
						if (rcGetCon(s, dir) != RC_NOT_CONNECTED)
						{
							const int ax = cx + rcGetDirOffsetX(dir);
							const int ay = cy + rcGetDirOffsetY(dir);
							const int ai = (int)chf.cells[ax+ay*w].index + rcGetCon(s, dir);
							// 当前方向上连接的 layer 
							unsigned char alid = srcReg[ai] != 0xff ? regs[srcReg[ai]].layerId : 0xff;
							// Portal mask
							if (chf.areas[ai] != RC_NULL_AREA && lid != alid)
							{
								// 如果不是同一个 layer
								portal |= (unsigned char)(1<<dir);
								// Update height so that it matches on both sides of the portal.
								const rcCompactSpan& as = chf.spans[ai];
								// 如果 span 的地面高度大于 layer 最小高度
								if (as.y > hmin)
									layer->heights[idx] = rcMax(layer->heights[idx], (unsigned char)(as.y - hmin));
							}
							// Valid connection mask
							if (chf.areas[ai] != RC_NULL_AREA && lid == alid)
							{
								const int nx = ax - borderSize;
								const int ny = ay - borderSize;
								// 如果是同一个 layer
								if (nx >= 0 && ny >= 0 && nx < lw && ny < lh)
									con |= (unsigned char)(1<<dir);
							}
						}
					}
				
					// 高4位保存外部连接方向，低4位保存内部连接方向
					layer->cons[idx] = (portal << 4) | con;
				}
			}
		}
		
		if (layer->minx > layer->maxx)
			layer->minx = layer->maxx = 0;
		if (layer->miny > layer->maxy)
			layer->miny = layer->maxy = 0;
	}
	
	return true;
}
