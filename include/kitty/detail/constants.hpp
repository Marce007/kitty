/* kitty: C++ truth table library
 * Copyright (C) 2017  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*! \cond PRIVATE */
#pragma once

#include <cstdint>
#include <vector>

namespace kitty
{

namespace detail
{

static constexpr uint64_t projections[] = {0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000};

static constexpr uint64_t projections_neg[] = {0x5555555555555555, 0x3333333333333333, 0x0f0f0f0f0f0f0f0f, 0x00ff00ff00ff00ff, 0x0000ffff0000ffff, 0x00000000ffffffff};

static constexpr uint64_t masks[] = {0x0000000000000001, 0x0000000000000003, 0x000000000000000f, 0x00000000000000ff, 0x000000000000ffff, 0x00000000ffffffff, 0xffffffffffffffff};

static constexpr uint64_t permutation_masks[][3] = {
    {0x9999999999999999, 0x2222222222222222, 0x4444444444444444},
    {0xc3c3c3c3c3c3c3c3, 0x0c0c0c0c0c0c0c0c, 0x3030303030303030},
    {0xf00ff00ff00ff00f, 0x00f000f000f000f0, 0x0f000f000f000f00},
    {0xff0000ffff0000ff, 0x0000ff000000ff00, 0x00ff000000ff0000},
    {0xffff00000000ffff, 0x00000000ffff0000, 0x0000ffff00000000}};

static constexpr uint64_t ppermutation_masks[][6][3] = {
    {{0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x9999999999999999, 0x2222222222222222, 0x4444444444444444},
     {0xa5a5a5a5a5a5a5a5, 0x0a0a0a0a0a0a0a0a, 0x5050505050505050},
     {0xaa55aa55aa55aa55, 0x00aa00aa00aa00aa, 0x5500550055005500},
     {0xaaaa5555aaaa5555, 0x0000aaaa0000aaaa, 0x5555000055550000},
     {0xaaaaaaaa55555555, 0x00000000aaaaaaaa, 0x5555555500000000}},
    {{0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0xc3c3c3c3c3c3c3c3, 0x0c0c0c0c0c0c0c0c, 0x3030303030303030},
     {0xcc33cc33cc33cc33, 0x00cc00cc00cc00cc, 0x3300330033003300},
     {0xcccc3333cccc3333, 0x0000cccc0000cccc, 0x3333000033330000},
     {0xcccccccc33333333, 0x00000000cccccccc, 0x3333333300000000}},
    {{0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0xf00ff00ff00ff00f, 0x00f000f000f000f0, 0x0f000f000f000f00},
     {0xf0f00f0ff0f00f0f, 0x0000f0f00000f0f0, 0x0f0f00000f0f0000},
     {0xf0f0f0f00f0f0f0f, 0x00000000f0f0f0f0, 0x0f0f0f0f00000000}},
    {{0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0xff0000ffff0000ff, 0x0000ff000000ff00, 0x00ff000000ff0000},
     {0xff00ff0000ff00ff, 0x00000000ff00ff00, 0x00ff00ff00000000}},
    {{0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0x0000000000000000, 0x0000000000000000, 0x0000000000000000},
     {0xffff00000000ffff, 0x00000000ffff0000, 0x0000ffff00000000}}};

static constexpr int32_t hex_to_int[] = {-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                                         -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                                         -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                                         0, 1, 2, 3, 4, 5, 6, 7, 8, 9, -1, -1, -1, -1, -1, -1,
                                         -1, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                                         -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                                         -1, 10, 11, 12, 13, 14, 15, -1, -1, -1, -1, -1, -1, -1, -1, -1,
                                         -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1};

/*! adjacent swap sequences (from 2 to 6 variables) */
static std::vector<uint8_t> swaps[] = {{0},
                                       {1, 0, 1, 0, 1},
                                       {2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2, 0, 2, 1, 0, 2, 0, 1, 2},
                                       {3, 2, 1, 0, 3, 0, 1, 2, 3, 1, 3, 2, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 1, 3, 2, 1, 0, 3, 0, 1, 2, 3, 0, 3, 2, 1, 0, 3, 0, 1, 2, 3, 1, 3, 2, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 1, 3, 2, 1, 0, 3, 0, 1, 2, 3, 0, 3, 2, 1, 0, 3, 0, 1, 2, 3, 1, 3, 2, 1, 0, 1, 0, 1, 2, 3, 2, 3, 2, 1, 0, 1, 0, 1, 2, 3, 1, 3, 2, 1, 0, 3, 0, 1, 2, 3},
                                       {4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 1, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 1, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 1, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 1, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 1, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 1, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4, 0, 4, 3, 2, 1, 0, 2, 0, 1, 2, 3, 4, 2, 4, 3, 2, 1, 0, 4, 0, 1, 2, 3, 4}};

/*! flip sequences (from 2 to 6 variables) */
static std::vector<uint8_t> flips[] = {{0, 1, 0},
                                       {0, 1, 0, 2, 0, 1, 0},
                                       {0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0},
                                       {0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0},
                                       {0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0, 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0}};

} // namespace detail
} // namespace kitty
/*! \endcond */
