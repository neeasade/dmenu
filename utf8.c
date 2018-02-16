/* utf8.c - dmenu
 *
 * Functions to retrieve utf8 character length and validity.
 */

#include <stddef.h>

#include "util.h" // TODO: question the necessity of the BETWEEN macro

#define UTF_INVALID 0xFFFD
#define UTF_SIZ     4

static const unsigned char utfbyte[UTF_SIZ + 1] = {0x80,    0, 0xC0, 0xE0, 0xF0};
static const unsigned char utfmask[UTF_SIZ + 1] = {0xC0, 0x80, 0xE0, 0xF0, 0xF8};
static const long utfmin[UTF_SIZ + 1] = {       0,    0,  0x80,  0x800,  0x10000};
static const long utfmax[UTF_SIZ + 1] = {0x10FFFF, 0x7F, 0x7FF, 0xFFFF, 0x10FFFF};

static long
utf8decodebyte(const char c, size_t *i)
{
	for (*i = 0; *i < (UTF_SIZ + 1); ++(*i))
		if (((unsigned char)c & utfmask[*i]) == utfbyte[*i])
			return (unsigned char)c & ~utfmask[*i];

	return 0;
}

static size_t
utf8validate(long *u, size_t i)
{
	if (!BETWEEN(*u, utfmin[i], utfmax[i]) || BETWEEN(*u, 0xD800, 0xDFFF))
		*u = UTF_INVALID;
	for (i = 1; *u > utfmax[i]; ++i)
		;
	return i;
}

size_t
utf8decode(const char *c, long *u)
{
	size_t i, j, len, type;
	long udecoded;

	*u = UTF_INVALID;
	udecoded = utf8decodebyte(c[0], &len);

	if (!BETWEEN(len, 1, UTF_SIZ))
		return 1;

	for (i = 1, j = 1; i < UTF_SIZ && j < len; ++i, ++j) {
		udecoded = (udecoded << 6) | utf8decodebyte(c[i], &type);
		if (type)
			return j;
	}

	if (j < len)
		return 0;

	*u = udecoded;
	utf8validate(u, len);

	return len;
}
