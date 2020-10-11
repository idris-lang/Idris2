#include "casts.h"
#include <inttypes.h>

Value *cast_i32_to_Bits8(Value *input)
{
	Value_Int8 *retVal = (Value_Int8 *)newValue();
	retVal->header.tag = INT8_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->i8 = (int8_t)from->i32;

	return (Value *)retVal;
}

Value *cast_i32_to_Bits16(Value *input)
{
	Value_Int16 *retVal = (Value_Int16 *)newValue();
	retVal->header.tag = INT16_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->i16 = (int16_t)from->i32;

	return (Value *)retVal;
}
Value *cast_i32_to_Bits32(Value *input)
{
	return input;
}
Value *cast_i32_to_Bits64(Value *input)
{
	return cast_i32_to_i64(input);
}

Value *cast_i32_to_i64(Value *input)
{
	Value_Int64 *retVal = (Value_Int64 *)newValue();
	retVal->header.tag = INT64_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->i64 = (int64_t)from->i32;

	return (Value *)retVal;
}

Value *cast_i32_to_double(Value *input)
{
	Value_Double *retVal = (Value_Double *)newValue();
	retVal->header.tag = DOUBLE_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->d = (double)from->i32;

	return (Value *)retVal;
}

Value *cast_i32_to_char(Value *input)
{
	Value_Char *retVal = (Value_Char *)newValue();
	retVal->header.tag = CHAR_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->c = (char)from->i32;

	return (Value *)retVal;
}

Value *cast_i32_to_string(Value *input)
{
	Value_String *retVal = (Value_String *)newValue();
	retVal->header.tag = STRING_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	int l = snprintf(NULL, 0, "%i", from->i32);
	retVal->str = malloc((l + 1) * sizeof(char));
	memset(retVal->str, 0, l + 1);
	sprintf(retVal->str, "%i", from->i32);

	return (Value *)retVal;
}

Value *cast_i64_to_Bits8(Value *input)
{
	Value_Int8 *retVal = (Value_Int8 *)newValue();
	retVal->header.tag = INT8_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->i8 = (int8_t)from->i64;

	return (Value *)retVal;
}
Value *cast_i64_to_Bits16(Value *input)
{
	Value_Int16 *retVal = (Value_Int16 *)newValue();
	retVal->header.tag = INT16_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->i16 = (int16_t)from->i64;

	return (Value *)retVal;
}
Value *cast_i64_to_Bits32(Value *input)
{
	return cast_i64_to_i32(input);
}

Value *cast_i64_to_Bits64(Value *input)
{
	return input;
}

Value *cast_i64_to_i32(Value *input)
{
	Value_Int32 *retVal = (Value_Int32 *)newValue();
	retVal->header.tag = INT32_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->i32 = (int32_t)from->i64;

	return (Value *)retVal;
}

Value *cast_i64_to_double(Value *input)
{
	Value_Double *retVal = (Value_Double *)newValue();
	retVal->header.tag = DOUBLE_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->d = (double)from->i64;

	return (Value *)retVal;
}

Value *cast_i64_to_char(Value *input)
{
	Value_Char *retVal = (Value_Char *)newValue();
	retVal->header.tag = CHAR_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->c = (char)from->i64;

	return (Value *)retVal;
}

Value *cast_i64_to_string(Value *input)
{
	Value_String *retVal = (Value_String *)newValue();
	retVal->header.tag = STRING_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	int l = snprintf(NULL, 0, "%" PRIu64 "", from->i64);
	retVal->str = malloc((l + 1) * sizeof(char));
	memset(retVal->str, 0, l + 1);
	sprintf(retVal->str, "%" PRIu64 "", from->i64);

	return (Value *)retVal;
}

Value *cast_double_to_Bits8(Value *input)
{
	Value_Int8 *retVal = (Value_Int8 *)newValue();
	retVal->header.tag = INT8_TAG;
	Value_Double *from = (Value_Double *)input;
	retVal->i8 = (int8_t)from->d;

	return (Value *)retVal;
}
Value *cast_double_to_Bits16(Value *input)
{
	Value_Int16 *retVal = (Value_Int16 *)newValue();
	retVal->header.tag = INT16_TAG;
	Value_Double *from = (Value_Double *)input;
	retVal->i16 = (int16_t)from->d;

	return (Value *)retVal;
}
Value *cast_double_to_Bits32(Value *input)
{
	return cast_double_to_i32(input);
}
Value *cast_double_to_Bits64(Value *input)
{
	return cast_double_to_i64(input);
}
Value *cast_double_to_i32(Value *input)
{
	Value_Int32 *retVal = (Value_Int32 *)newValue();
	retVal->header.tag = INT32_TAG;
	Value_Double *from = (Value_Double *)input;
	retVal->i32 = (int32_t)from->d;

	return (Value *)retVal;
}

Value *cast_double_to_i64(Value *input)
{
	Value_Int64 *retVal = (Value_Int64 *)newValue();
	retVal->header.tag = INT64_TAG;
	Value_Double *from = (Value_Double *)input;
	retVal->i64 = (int64_t)from->d;

	return (Value *)retVal;
}

Value *cast_double_to_char(Value *input)
{
	Value_Char *retVal = (Value_Char *)newValue();
	retVal->header.tag = CHAR_TAG;
	Value_Double *from = (Value_Double *)input;
	retVal->c = (char)from->d;

	return (Value *)retVal;
}

Value *cast_double_to_string(Value *input)
{
	Value_String *retVal = (Value_String *)newValue();
	retVal->header.tag = STRING_TAG;
	Value_Double *from = (Value_Double *)input;
	int l = snprintf(NULL, 0, "%f", from->d);
	retVal->str = malloc((l + 1) * sizeof(char));
	memset(retVal->str, 0, l + 1);
	sprintf(retVal->str, "%f", from->d);

	return (Value *)retVal;
}

Value *cast_char_to_Bits8(Value *input)
{
	Value_Int8 *retVal = (Value_Int8 *)newValue();
	retVal->header.tag = INT8_TAG;
	Value_Char *from = (Value_Char *)input;
	retVal->i8 = (int8_t)from->c;

	return (Value *)retVal;
}
Value *cast_char_to_Bits16(Value *input)
{
	Value_Int16 *retVal = (Value_Int16 *)newValue();
	retVal->header.tag = INT16_TAG;
	Value_Char *from = (Value_Char *)input;
	retVal->i16 = (int16_t)from->c;

	return (Value *)retVal;
}
Value *cast_char_to_Bits32(Value *input)
{
	return cast_char_to_i32(input);
}
Value *cast_char_to_Bits64(Value *input)
{
	return cast_char_to_i64(input);
}
Value *cast_char_to_i32(Value *input)
{
	Value_Int32 *retVal = (Value_Int32 *)newValue();
	retVal->header.tag = INT32_TAG;
	Value_Char *from = (Value_Char *)input;
	retVal->i32 = (int32_t)from->c;

	return (Value *)retVal;
}

Value *cast_char_to_i64(Value *input)
{
	Value_Int64 *retVal = (Value_Int64 *)newValue();
	retVal->header.tag = INT64_TAG;
	Value_Char *from = (Value_Char *)input;
	retVal->i64 = (int64_t)from->c;

	return (Value *)retVal;
}

Value *cast_char_to_double(Value *input)
{
	Value_Double *retVal = (Value_Double *)newValue();
	retVal->header.tag = DOUBLE_TAG;
	Value_Char *from = (Value_Char *)input;
	retVal->d = (double)from->c;

	return (Value *)retVal;
}

Value *cast_char_to_string(Value *input)
{
	Value_String *retVal = (Value_String *)newValue();
	retVal->header.tag = STRING_TAG;
	Value_Char *from = (Value_Char *)input;
	retVal->str = malloc(2 * sizeof(char));
	memset(retVal->str, 0, 2);
	retVal->str[0] = from->c;

	return (Value *)retVal;
}

Value *cast_string_to_Bits8(Value *input)
{
	Value_Int8 *retVal = (Value_Int8 *)newValue();
	retVal->header.tag = INT8_TAG;
	Value_String *from = (Value_String *)input;
	retVal->i8 = (uint8_t)atoi(from->str);

	return (Value *)retVal;
}
Value *cast_string_to_Bits16(Value *input)
{
	Value_Int16 *retVal = (Value_Int16 *)newValue();
	retVal->header.tag = INT16_TAG;
	Value_String *from = (Value_String *)input;
	retVal->i16 = (uint16_t)atoi(from->str);

	return (Value *)retVal;
}
Value *cast_string_to_Bits32(Value *input)
{
	return cast_string_to_i32(input);
}
Value *cast_string_to_Bits64(Value *input)
{
	return cast_string_to_i64(input);
}
Value *cast_string_to_i32(Value *input)
{
	Value_Int32 *retVal = (Value_Int32 *)newValue();
	retVal->header.tag = INT32_TAG;
	Value_String *from = (Value_String *)input;
	retVal->i32 = atoi(from->str);

	return (Value *)retVal;
}

Value *cast_string_to_i64(Value *input)
{
	Value_Int64 *retVal = (Value_Int64 *)newValue();
	retVal->header.tag = INT64_TAG;
	Value_String *from = (Value_String *)input;
	retVal->i64 = atoi(from->str);

	return (Value *)retVal;
}

Value *cast_string_to_double(Value *input)
{
	Value_Double *retVal = (Value_Double *)newValue();
	retVal->header.tag = DOUBLE_TAG;
	Value_String *from = (Value_String *)input;
	retVal->d = atof(from->str);

	return (Value *)retVal;
}

Value *cast_string_to_char(Value *input)
{
	Value_Char *retVal = (Value_Char *)newValue();
	retVal->header.tag = CHAR_TAG;
	Value_String *from = (Value_String *)input;
	retVal->c = from->str[0];

	return (Value *)retVal;
}

// Bits cast
// autogenerated using Ruby

/*  conversions from Bits8  */
Value *cast_Bits8_to_Bits16(Value *input)
{
	Value_Int16 *retVal = (Value_Int16 *)newValue();
	retVal->header.tag = INT16_TAG;
	Value_Int8 *from = (Value_Int8 *)input;
	retVal->i16 = (int16_t)from->i8;

	return (Value *)retVal;
}
Value *cast_Bits8_to_Bits32(Value *input)
{
	Value_Int32 *retVal = (Value_Int32 *)newValue();
	retVal->header.tag = INT32_TAG;
	Value_Int8 *from = (Value_Int8 *)input;
	retVal->i32 = (int32_t)from->i8;

	return (Value *)retVal;
}
Value *cast_Bits8_to_Bits64(Value *input)
{
	Value_Int64 *retVal = (Value_Int64 *)newValue();
	retVal->header.tag = INT64_TAG;
	Value_Int8 *from = (Value_Int8 *)input;
	retVal->i64 = (int64_t)from->i8;

	return (Value *)retVal;
}
Value *cast_Bits8_to_i32(Value *input)
{
	Value_Int32 *retVal = (Value_Int32 *)newValue();
	retVal->header.tag = INT32_TAG;
	Value_Int8 *from = (Value_Int8 *)input;
	retVal->i32 = (int32_t)from->i8;

	return (Value *)retVal;
}
Value *cast_Bits8_to_i64(Value *input)
{
	Value_Int64 *retVal = (Value_Int64 *)newValue();
	retVal->header.tag = INT64_TAG;
	Value_Int8 *from = (Value_Int8 *)input;
	retVal->i64 = (int64_t)from->i8;

	return (Value *)retVal;
}
Value *cast_Bits8_to_double(Value *input)
{
	Value_Double *retVal = (Value_Double *)newValue();
	retVal->header.tag = DOUBLE_TAG;
	Value_Int8 *from = (Value_Int8 *)input;
	retVal->d = (double)from->i8;

	return (Value *)retVal;
}

Value *cast_Bits8_to_char(Value *input)
{
	Value_Char *retVal = (Value_Char *)newValue();
	retVal->header.tag = CHAR_TAG;
	Value_Int8 *from = (Value_Int8 *)input;
	retVal->c = (char)from->i8;

	return (Value *)retVal;
}
Value *cast_Bits8_to_string(Value *input)
{
	Value_String *retVal = (Value_String *)newValue();
	retVal->header.tag = STRING_TAG;
	Value_Int8 *from = (Value_Int8 *)input;
	int l = snprintf(NULL, 0, "%" PRIu8 "", from->i8);
	retVal->str = malloc((l + 1) * sizeof(char));
	memset(retVal->str, 0, l + 1);
	sprintf(retVal->str, "%" PRIu8 "", from->i8);

	return (Value *)retVal;
}

/*  conversions from Bits16  */
Value *cast_Bits16_to_Bits8(Value *input)
{
	Value_Int8 *retVal = (Value_Int8 *)newValue();
	retVal->header.tag = INT8_TAG;
	Value_Int16 *from = (Value_Int16 *)input;
	retVal->i8 = (int8_t)from->i16;

	return (Value *)retVal;
}
Value *cast_Bits16_to_Bits32(Value *input)
{
	Value_Int32 *retVal = (Value_Int32 *)newValue();
	retVal->header.tag = INT32_TAG;
	Value_Int16 *from = (Value_Int16 *)input;
	retVal->i32 = (int32_t)from->i16;

	return (Value *)retVal;
}
Value *cast_Bits16_to_Bits64(Value *input)
{
	Value_Int64 *retVal = (Value_Int64 *)newValue();
	retVal->header.tag = INT64_TAG;
	Value_Int16 *from = (Value_Int16 *)input;
	retVal->i64 = (int64_t)from->i16;

	return (Value *)retVal;
}
Value *cast_Bits16_to_i32(Value *input)
{
	Value_Int32 *retVal = (Value_Int32 *)newValue();
	retVal->header.tag = INT32_TAG;
	Value_Int16 *from = (Value_Int16 *)input;
	retVal->i32 = (int32_t)from->i16;

	return (Value *)retVal;
}
Value *cast_Bits16_to_i64(Value *input)
{
	Value_Int64 *retVal = (Value_Int64 *)newValue();
	retVal->header.tag = INT64_TAG;
	Value_Int16 *from = (Value_Int16 *)input;
	retVal->i64 = (int64_t)from->i16;

	return (Value *)retVal;
}
Value *cast_Bits16_to_double(Value *input)
{
	Value_Double *retVal = (Value_Double *)newValue();
	retVal->header.tag = DOUBLE_TAG;
	Value_Int16 *from = (Value_Int16 *)input;
	retVal->d = (double)from->i16;

	return (Value *)retVal;
}

Value *cast_Bits16_to_char(Value *input)
{
	Value_Char *retVal = (Value_Char *)newValue();
	retVal->header.tag = CHAR_TAG;
	Value_Int16 *from = (Value_Int16 *)input;
	retVal->c = (char)from->i16;

	return (Value *)retVal;
}
Value *cast_Bits16_to_string(Value *input)
{
	Value_String *retVal = (Value_String *)newValue();
	retVal->header.tag = STRING_TAG;
	Value_Int16 *from = (Value_Int16 *)input;
	int l = snprintf(NULL, 0, "%" PRIu16 "", from->i16);
	retVal->str = malloc((l + 1) * sizeof(char));
	memset(retVal->str, 0, l + 1);
	sprintf(retVal->str, "%" PRIu16 "", from->i16);

	return (Value *)retVal;
}

/*  conversions from Bits32  */
Value *cast_Bits32_to_Bits8(Value *input)
{
	Value_Int8 *retVal = (Value_Int8 *)newValue();
	retVal->header.tag = INT8_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->i8 = (int8_t)from->i32;

	return (Value *)retVal;
}
Value *cast_Bits32_to_Bits16(Value *input)
{
	Value_Int16 *retVal = (Value_Int16 *)newValue();
	retVal->header.tag = INT16_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->i16 = (int16_t)from->i32;

	return (Value *)retVal;
}
Value *cast_Bits32_to_Bits64(Value *input)
{
	Value_Int64 *retVal = (Value_Int64 *)newValue();
	retVal->header.tag = INT64_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->i64 = (int64_t)from->i32;

	return (Value *)retVal;
}
Value *cast_Bits32_to_i32(Value *input)
{
	return input;
}
Value *cast_Bits32_to_i64(Value *input)
{
	Value_Int64 *retVal = (Value_Int64 *)newValue();
	retVal->header.tag = INT64_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->i64 = (int64_t)from->i32;

	return (Value *)retVal;
}
Value *cast_Bits32_to_double(Value *input)
{
	Value_Double *retVal = (Value_Double *)newValue();
	retVal->header.tag = DOUBLE_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->d = (double)from->i32;

	return (Value *)retVal;
}

Value *cast_Bits32_to_char(Value *input)
{
	Value_Char *retVal = (Value_Char *)newValue();
	retVal->header.tag = CHAR_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	retVal->c = (char)from->i32;

	return (Value *)retVal;
}
Value *cast_Bits32_to_string(Value *input)
{
	Value_String *retVal = (Value_String *)newValue();
	retVal->header.tag = STRING_TAG;
	Value_Int32 *from = (Value_Int32 *)input;
	int l = snprintf(NULL, 0, "%" PRIu32 "", (uint32_t)from->i32);
	retVal->str = malloc((l + 1) * sizeof(char));
	memset(retVal->str, 0, l + 1);
	sprintf(retVal->str, "%" PRIu32 "", (uint32_t)from->i32);

	return (Value *)retVal;
}

/*  conversions from Bits64  */
Value *cast_Bits64_to_Bits8(Value *input)
{
	Value_Int8 *retVal = (Value_Int8 *)newValue();
	retVal->header.tag = INT8_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->i8 = (int8_t)from->i64;

	return (Value *)retVal;
}
Value *cast_Bits64_to_Bits16(Value *input)
{
	Value_Int16 *retVal = (Value_Int16 *)newValue();
	retVal->header.tag = INT16_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->i16 = (int16_t)from->i64;

	return (Value *)retVal;
}
Value *cast_Bits64_to_Bits32(Value *input)
{
	Value_Int32 *retVal = (Value_Int32 *)newValue();
	retVal->header.tag = INT32_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->i32 = (int32_t)from->i64;

	return (Value *)retVal;
}
Value *cast_Bits64_to_i32(Value *input)
{
	Value_Int32 *retVal = (Value_Int32 *)newValue();
	retVal->header.tag = INT32_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->i32 = (int32_t)from->i64;

	return (Value *)retVal;
}
Value *cast_Bits64_to_i64(Value *input)
{
	return input;
}
Value *cast_Bits64_to_double(Value *input)
{
	Value_Double *retVal = (Value_Double *)newValue();
	retVal->header.tag = DOUBLE_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->d = (double)from->i64;

	return (Value *)retVal;
}

Value *cast_Bits64_to_char(Value *input)
{
	Value_Char *retVal = (Value_Char *)newValue();
	retVal->header.tag = CHAR_TAG;
	Value_Int64 *from = (Value_Int64 *)input;
	retVal->c = (char)from->i64;

	return (Value *)retVal;
}
Value *cast_Bits64_to_string(Value *input)
{
	return cast_i64_to_string(input);
}
