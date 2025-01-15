

local StrToNumber = tonumber; 
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 43) then
					if (Enum <= 21) then
						if (Enum <= 10) then
							if (Enum <= 4) then
								if (Enum <= 1) then
									if (Enum == 0) then
										local A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
									else
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
									end
								elseif (Enum <= 2) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif (Enum > 3) then
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum <= 7) then
								if (Enum <= 5) then
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
								elseif (Enum == 6) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 8) then
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							elseif (Enum == 9) then
								local B = Inst[3];
								local K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							end
						elseif (Enum <= 15) then
							if (Enum <= 12) then
								if (Enum == 11) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 13) then
								local A = Inst[2];
								local T = Stk[A];
								local B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							elseif (Enum > 14) then
								if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 18) then
							if (Enum <= 16) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum > 17) then
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							elseif (Stk[Inst[2]] <= Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 19) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum == 20) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 32) then
						if (Enum <= 26) then
							if (Enum <= 23) then
								if (Enum == 22) then
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum <= 24) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							elseif (Enum == 25) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
							end
						elseif (Enum <= 29) then
							if (Enum <= 27) then
								local A = Inst[2];
								Stk[A] = Stk[A]();
							elseif (Enum > 28) then
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 30) then
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 31) then
							local Results;
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 37) then
						if (Enum <= 34) then
							if (Enum > 33) then
								Stk[Inst[2]] = Stk[Inst[3]];
							else
								local Edx;
								local Results;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Stk[A + 1])};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 35) then
							local A;
							local K;
							local B;
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum > 36) then
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Inst[3] do
								Insert(T, Stk[Idx]);
							end
						else
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 40) then
						if (Enum <= 38) then
							local A;
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 39) then
							Stk[Inst[2]]();
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 41) then
						local A = Inst[2];
						Stk[A](Stk[A + 1]);
					elseif (Enum > 42) then
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 65) then
					if (Enum <= 54) then
						if (Enum <= 48) then
							if (Enum <= 45) then
								if (Enum > 44) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 46) then
								local A = Inst[2];
								local Results = {Stk[A](Stk[A + 1])};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 47) then
								do
									return;
								end
							else
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 51) then
							if (Enum <= 49) then
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Enum > 50) then
								Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
							else
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							end
						elseif (Enum <= 52) then
							local B;
							local A;
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 53) then
							local A;
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 34) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum <= 59) then
						if (Enum <= 56) then
							if (Enum > 55) then
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = #Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 57) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 58) then
							local Results;
							local Edx;
							local Results, Limit;
							local B;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A;
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 62) then
						if (Enum <= 60) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum > 61) then
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 63) then
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
					elseif (Enum > 64) then
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
					else
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 76) then
					if (Enum <= 70) then
						if (Enum <= 67) then
							if (Enum > 66) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 68) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						elseif (Enum > 69) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
						end
					elseif (Enum <= 73) then
						if (Enum <= 71) then
							local A;
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						elseif (Enum == 72) then
							local B;
							local A;
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							Stk[Inst[2]] = #Stk[Inst[3]];
						end
					elseif (Enum <= 74) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 75) then
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A;
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 81) then
					if (Enum <= 78) then
						if (Enum > 77) then
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 79) then
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif (Enum > 80) then
						Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					else
						Stk[Inst[2]] = {};
					end
				elseif (Enum <= 84) then
					if (Enum <= 82) then
						local B;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]]();
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 83) then
						if (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A;
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
					end
				elseif (Enum <= 85) then
					Stk[Inst[2]] = Inst[3] ~= 0;
				elseif (Enum > 86) then
					if (Stk[Inst[2]] ~= Inst[4]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				else
					Stk[Inst[2]] = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!523Q00030A3Q006C6F6164737472696E67034D012Q00096C6F63616C20456E762C20757076616C756573203D203Q2E0A096C6F63616C206E6577203D206E657770726F78792874727565290A096C6F63616C206D74203D206765746D6574617461626C65286E6577290A096D742E2Q5F6D6574617461626C65203D206E65770A096D742E2Q5F656E7669726F6E6D656E74203D206E65770A096D742E2Q5F696E646578203D2066756E6374696F6E28742C6B292072657475726E20456E765B6B5D206F7220757076616C7565735B6B5D20656E640A096D742E2Q5F6E6577696E646578203D2066756E6374696F6E28742C6B2C76290A2Q092Q2D69662072617767657428757076616C7565732C6B29207468656E2072657475726E2072617773657428757076616C7565732C6B2C762920656E640A2Q09456E765B6B5D203D20760A09656E640A72657475726E207365746D6574617461626C65287B7D2C6D74290A034Q0003023Q005F4703063Q0049676E6F7265030D3Q0057616974506572416D6F756E74025Q00407F4003113Q0053656E644E6F74696669636174696F6E73002Q01030B3Q00436F6E736F6C654C6F6773010003043Q0067616D6503083Q0049734C6F6164656403043Q007461736B03043Q007761697403083Q0053652Q74696E677303073Q00506C617965727303093Q0049676E6F7265204D65030D3Q0049676E6F7265204F7468657273030C3Q0049676E6F726520542Q6F6C7303063Q004D657368657303063Q004E6F4D65736803093Q004E6F5465787475726503073Q0044657374726F7903063Q00496D6167657303093Q00496E76697369626C65030A3Q004578706C6F73696F6E7303073Q00536D612Q6C657203093Q005061727469636C6573030A3Q00546578744C6162656C73030C3Q004C6F7765725175616C69747903093Q004D657368506172747303053Q004F7468657203073Q0046505320436170024Q00F069F84003113Q004E6F2043616D65726120452Q6665637473030A3Q004E6F20436C6F7468657303123Q004C6F77205761746572204772617068696373030A3Q004E6F20536861646F7773030D3Q004C6F772052656E646572696E6703113Q004C6F77205175616C69747920506172747303123Q004C6F77205175616C697479204D6F64656C73030F3Q005265736574204D6174657269616C7303173Q004C6F776572205175616C697479204D6573685061727473030A3Q004765745365727669636503083Q004C69676874696E67030A3Q0053746172746572477569030F3Q004D6174657269616C53657276696365030B3Q004C6F63616C506C61796572030F3Q005061727469636C65456D692Q74657203053Q00547261696C03053Q00536D6F6B6503043Q004669726503083Q00537061726B6C657303073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C6503073Q005B74617875735D03043Q005465787403163Q004C6F6164696E672046505320422Q6F737465723Q2E03083Q004475726174696F6E03043Q006D61746803043Q006875676503073Q0042752Q746F6E3103043Q004F6B617903093Q00636F726F7574696E6503043Q007772617003053Q007063612Q6C030F3Q0044657363656E64616E74412Q64656403073Q00436F2Q6E656374030E3Q0047657444657363656E64616E747303093Q00436865636B696E6720030D3Q0020496E7374616E6365733Q2E026Q002E4003043Q007761726E03053Q00706169727303053Q007072696E7403073Q004C6F616465642003013Q002F03133Q0046505320422Q6F73746572204C6F6164656421031D3Q00682Q7470733A2Q2F646973636F72642E2Q672F48562Q324E504D7A717A0010012Q00120C3Q00013Q00122Q000100013Q00122Q000200023Q00122Q000300036Q0001000300024Q00028Q00035Q00122Q000400043Q00202Q00040004000500062Q0004000E0001000100044D3Q000E0001001227000400044Q005000055Q001051000400050005001227000400043Q00200800040004000600061D000400140001000100044D3Q00140001001227000400043Q003024000400060007001227000400043Q0020080004000400080026530004001A0001000900044D3Q001A0001001227000400043Q00302400040008000A001227000400043Q00200800040004000B002653000400200001000900044D3Q00200001001227000400043Q0030240004000B000C0012270004000D3Q00203D00040004000E2Q002C00040002000200061D0004002D0001000100044D3Q002D00010012270004000F3Q0020520004000400104Q00040001000100122Q0004000D3Q00202Q00040004000E4Q00040002000200062Q0004002500013Q00044D3Q00250001001227000400043Q00200800040004001100061D000400630001000100044D3Q00630001001227000400044Q000500053Q00084Q00063Q000300302Q00060013000A00302Q00060014000A00302Q00060015000A00102Q0005001200064Q00063Q000300302Q00060017000C00302Q00060018000C00302Q00060019000C0010510005001600062Q000100063Q000200302Q0006001B000A00302Q00060019000C00102Q0005001A00064Q00063Q000300302Q0006001D000A00302Q0006001B000C00302Q00060019000C00102Q0005001C00064Q00063Q00020030240006001B000A00300200060019000C00102Q0005001E00064Q00063Q000300302Q00060020000C00302Q0006001B000C00302Q00060019000C00102Q0005001F00064Q00063Q000500302Q00060020000A00302Q0006001B000C00302400060018000C00301A00060017000C00302Q00060019000C00102Q0005002100064Q00063Q000A00302Q00060023002400302Q00060025000A00302Q00060026000A00302Q00060027000A00302Q00060028000A00302Q00060029000A0030240006002A000A00302B0006002B000A00302Q0006002C000A00302Q0006002D000A00102Q00050022000600102Q0004001100050012270004000D3Q00204800040004002E00122Q000600126Q00040006000200122Q0005000D3Q00202Q00050005002E00122Q0007002F6Q00050007000200122Q0006000D3Q00202Q00060006002E00122Q000800304Q001000060008000200120E0007000D3Q00202Q00070007002E00122Q000900316Q00070009000200202Q0008000400324Q000900053Q00122Q000A00333Q00122Q000B00343Q00122Q000C00353Q00122Q000D00363Q001256000E00374Q000D000900050001000635000A3Q000100022Q00223Q00044Q00223Q00083Q000233000B00013Q000635000C0002000100052Q00223Q00044Q00223Q000A4Q00223Q00084Q00223Q000B4Q00223Q00093Q001227000D00043Q002008000D000D000800061E000D009300013Q00044D3Q0093000100203D000D00060038001213000F00396Q00103Q000400302Q0010003A003B00302Q0010003C003D00122Q0011003F3Q00202Q00110011004000102Q0010003E001100302Q0010004100424Q000D00100001001227000D00433Q002008000D000D0044001227000E00454Q002C000D00020002000635000E0003000100012Q00223Q00064Q0036000D0002000100122Q000D00433Q00202Q000D000D004400122Q000E00456Q000D00020002000635000E0004000100022Q00223Q00054Q00223Q00064Q0036000D0002000100122Q000D00433Q00202Q000D000D004400122Q000E00456Q000D00020002000635000E0005000100012Q00223Q00064Q0036000D0002000100122Q000D00433Q00202Q000D000D004400122Q000E00456Q000D00020002000635000E0006000100022Q00223Q00074Q00223Q00064Q0036000D0002000100122Q000D00433Q00202Q000D000D004400122Q000E00456Q000D00020002000635000E0007000100012Q00223Q00064Q0029000D00020001001227000D000D3Q002008000D000D004600203D000D000D0047000635000F0008000100012Q00223Q000C4Q0034000D000F000100122Q000D000D3Q00202Q000D000D00484Q000D0002000200122Q000E00043Q00202Q000E000E000600062Q000E00C60001000100044D3Q00C60001001256000E00073Q001227000F00043Q002008000F000F000600061D000F00CB0001000100044D3Q00CB0001001256000F00073Q001227001000043Q00200800100010000800061E001000DB00013Q00044D3Q00DB000100203D001000060038001231001200396Q00133Q000400302Q0013003A003B00122Q001400496Q0015000D3Q00122Q0016004A4Q002300140014001600102Q0013003C001400302Q0013003E004B00302Q0013004100424Q001000130001001227001000043Q00200800100010000B00061E001000E500013Q00044D3Q00E500010012270010004C3Q001230001100496Q0012000D3Q00122Q0013004A6Q0011001100134Q0010000200010012270010004D4Q00220011000D4Q002E00100002001200044D3Q00FD00012Q00220015000C4Q0022001600144Q002900150002000100061F001300FD0001000F00044D3Q00FD00010012270015000F3Q00204A0015001500104Q00150001000100122Q001500043Q00202Q00150015000B00062Q001500FC00013Q00044D3Q00FC00010012270015004E3Q0012370016004F6Q001700133Q00122Q001800506Q0019000D6Q0016001600194Q0015000200012Q0038000F000F000E000612001000E90001000200044D3Q00E9000100203D001000060038001213001200396Q00133Q000400302Q0013003A003B00302Q0013003C005100122Q0014003F3Q00202Q00140014004000102Q0013003E001400302Q0013004100424Q0010001300010012270010004C3Q001256001100514Q001C00100002000100122Q0010004C3Q00122Q001100526Q0010000200016Q00013Q00093Q00043Q0003053Q007061697273030A3Q00476574506C617965727303093Q00436861726163746572030E3Q00497344657363656E64616E744F6601183Q00123A000100016Q00025Q00202Q0002000200024Q000200036Q00013Q000300044Q001300012Q0003000600013Q00060F000500130001000600044D3Q0013000100200800060005000300061E0006001300013Q00044D3Q0013000100203D00063Q00040020080008000500032Q001000060008000200061E0006001300013Q00044D3Q001300012Q0055000600014Q0017000600023Q000612000100060001000200044D3Q000600012Q005500016Q0017000100024Q002F3Q00017Q00043Q0003053Q00706169727303023Q005F4703063Q0049676E6F7265030E3Q00497344657363656E64616E744F6601113Q001221000100013Q00122Q000200023Q00202Q0002000200034Q00010002000300044Q000C000100203D00063Q00042Q0022000800054Q001000060008000200061E0006000C00013Q00044D3Q000C00012Q0055000600014Q0017000600023Q000612000100050001000200044D3Q000500012Q005500016Q0017000100024Q002F3Q00017Q00573Q00030E3Q00497344657363656E64616E744F6603023Q005F4703083Q0053652Q74696E677303073Q00506C6179657273030D3Q0049676E6F7265204F746865727303093Q0049676E6F7265204D6503093Q00436861726163746572030C3Q0049676E6F726520542Q6F6C732Q033Q00497341030C3Q004261636B7061636B4974656D03193Q0046696E644669727374416E636573746F72576869636849734103063Q0049676E6F726503053Q007461626C6503043Q0066696E6403043Q0074797065028Q00030D3Q00446174614D6F64656C4D65736803063Q004D657368657303063Q004E6F4D657368030B3Q005370656369616C4D65736803063Q004D6573684964034Q0003093Q004E6F5465787475726503093Q0054657874757265496403073Q0044657374726F7903093Q004E6F204D6573686573030C3Q0046616365496E7374616E636503063Q00496D6167657303093Q00496E76697369626C65030C3Q005472616E73706172656E6379026Q00F03F03053Q005368696E7903093Q004C6F7744657461696C030C3Q0053686972744772617068696303073Q004772617068696303093Q00436C612Q734E616D6503133Q00496E76697369626C65205061727469636C6573030C3Q004E6F205061727469636C657303053Q004F7468657203093Q005061727469636C657303073Q00456E61626C65640100030A3Q00506F7374452Q6665637403113Q004E6F2043616D65726120452Q666563747303093Q004578706C6F73696F6E03123Q00536D612Q6C6572204578706C6F73696F6E73030A3Q004578706C6F73696F6E7303073Q00536D612Q6C6572030D3Q00426C6173745072652Q73757265030B3Q00426C61737452616469757303143Q00496E76697369626C65204578706C6F73696F6E7303073Q0056697369626C65030D3Q004E6F204578706C6F73696F6E7303083Q00436C6F7468696E6703113Q0053757266616365412Q70656172616E636503083Q004261736557726170030A3Q004E6F20436C6F7468657303083Q00426173655061727403083Q004D6573685061727403113Q004C6F77205175616C69747920506172747303083Q004D6174657269616C03043Q00456E756D03073Q00506C6173746963030B3Q005265666C656374616E636503093Q00546578744C6162656C03093Q00776F726B737061636503183Q004C6F776572205175616C69747920546578744C6162656C73030A3Q00546578744C6162656C73030C3Q004C6F7765725175616C69747903043Q00466F6E74030A3Q00536F7572636553616E73030A3Q00546578745363616C656403083Q00526963685465787403083Q005465787453697A65026Q002C4003143Q00496E76697369626C6520546578744C6162656C73030D3Q004E6F20546578744C6162656C7303053Q004D6F64656C03123Q004C6F77205175616C697479204D6F64656C73030D3Q004C6576656C4F6644657461696C03153Q004C6F77205175616C697479204D657368506172747303093Q004D6573685061727473030E3Q0052656E646572466964656C697479027Q004003133Q00496E76697369626C65204D657368506172747303093Q00546578747572654944030C3Q004E6F204D657368506172747301B2022Q00203D00013Q00012Q000300036Q001000010003000200061D000100B10201000100044D3Q00B10201001227000100023Q00200800010001000300200800010001000400200800010001000500061E0001001000013Q00044D3Q001000012Q0003000100014Q002200026Q002C00010002000200061E0001001600013Q00044D3Q00160001001227000100023Q00200800010001000300200800010001000400200800010001000500061D000100B10201000100044D3Q00B10201001227000100023Q00200800010001000300200800010001000400200800010001000600061E0001002600013Q00044D3Q002600012Q0003000100023Q00200800010001000700061E0001002600013Q00044D3Q0026000100203D00013Q00012Q0003000300023Q0020080003000300072Q001000010003000200061E0001002C00013Q00044D3Q002C0001001227000100023Q00200800010001000300200800010001000400200800010001000600061D000100B10201000100044D3Q00B10201001227000100023Q00200800010001000300200800010001000400200800010001000800061E0001003C00013Q00044D3Q003C000100203D00013Q00090012560003000A4Q001000010003000200061D0001003C0001000100044D3Q003C000100203D00013Q000B0012560003000A4Q001000010003000200061E0001004200013Q00044D3Q00420001001227000100023Q00200800010001000300200800010001000400200800010001000800061D000100B10201000100044D3Q00B10201001227000100023Q00200800010001000C00061E0001005300013Q00044D3Q005300010012270001000D3Q00204000010001000E00122Q000200023Q00202Q00020002000C4Q00038Q00010003000200062Q000100530001000100044D3Q005300012Q0003000100034Q002200026Q002C00010002000200061E0001006200013Q00044D3Q00620001001227000100023Q00200800010001000C00061E0001006200013Q00044D3Q006200010012270001000F3Q001227000200023Q00200800020002000C2Q002C000100020002002653000100620001000D00044D3Q00620001001227000100023Q00200800010001000C2Q0049000100013Q002611000100B10201001000044D3Q00B1020100203D00013Q0009001256000300114Q001000010003000200061E0001008D00013Q00044D3Q008D0001001227000100023Q00200800010001000300200800010001001200200800010001001300061E0001007300013Q00044D3Q0073000100203D00013Q0009001256000300144Q001000010003000200061E0001007300013Q00044D3Q007300010030243Q00150016001227000100023Q00200800010001000300200800010001001200200800010001001700061E0001007F00013Q00044D3Q007F000100203D00013Q0009001256000300144Q001000010003000200061E0001007F00013Q00044D3Q007F00010030243Q00180016001227000100023Q00200800010001000300200800010001001200200800010001001900061D0001008A0001000100044D3Q008A0001001227000100023Q00200800010001000300200800010001001A00061E000100B102013Q00044D3Q00B1020100203D00013Q00192Q002900010002000100044D3Q00B1020100203D00013Q00090012560003001B4Q001000010003000200061E000100AA00013Q00044D3Q00AA0001001227000100023Q00200800010001000300200800010001001C00200800010001001D00061E0001009A00013Q00044D3Q009A00010030243Q001E001F0030243Q0020001F001227000100023Q00200800010001000300200800010001001C00200800010001002100061E000100A100013Q00044D3Q00A100010030243Q0020001F001227000100023Q00200800010001000300200800010001001C00200800010001001900061E000100B102013Q00044D3Q00B1020100203D00013Q00192Q002900010002000100044D3Q00B1020100203D00013Q0009001256000300224Q001000010003000200061E000100BF00013Q00044D3Q00BF0001001227000100023Q00200800010001000300200800010001001C00200800010001001D00061E000100B600013Q00044D3Q00B600010030243Q00230016001227000100023Q00200800010001000300200800010001001C00200800010001001900061E000100B102013Q00044D3Q00B1020100203D00013Q00192Q002900010002000100044D3Q00B102010012270001000D3Q00203900010001000E4Q000200043Q00202Q00033Q00244Q00010003000200062Q00012Q002Q013Q00044D4Q002Q01001227000100023Q00200800010001000300200800010001002500061D000100E60001000100044D3Q00E60001001227000100023Q00200800010001000300200800010001002600061D000100E60001000100044D3Q00E60001001227000100023Q00200800010001000300200800010001002700061E000100DB00013Q00044D3Q00DB0001001227000100023Q00200800010001000300200800010001002700200800010001002500061D000100E60001000100044D3Q00E60001001227000100023Q00200800010001000300200800010001002800061E000100E700013Q00044D3Q00E70001001227000100023Q00200800010001000300200800010001002800200800010001001D00061E000100E700013Q00044D3Q00E700010030243Q0029002A001227000100023Q00200800010001000300200800010001002700061E000100F200013Q00044D3Q00F20001001227000100023Q00200800010001000300200800010001002700200800010001002600061D000100FD0001000100044D3Q00FD0001001227000100023Q00200800010001000300200800010001002800061E000100B102013Q00044D3Q00B10201001227000100023Q00200800010001000300200800010001002800200800010001001900061E000100B102013Q00044D3Q00B1020100203D00013Q00192Q002900010002000100044D3Q00B1020100203D00013Q00090012560003002B4Q001000010003000200061E000100172Q013Q00044D3Q00172Q01001227000100023Q00200800010001000300200800010001002C00061D000100152Q01000100044D3Q00152Q01001227000100023Q00200800010001000300200800010001002700061E000100172Q013Q00044D3Q00172Q01001227000100023Q00200800010001000300200800010001002700200800010001002C00061E000100172Q013Q00044D3Q00172Q010030243Q0029002A00044D3Q00B1020100203D00013Q00090012560003002D4Q001000010003000200061E000100752Q013Q00044D3Q00752Q01001227000100023Q00200800010001000300200800010001002E00061D000100372Q01000100044D3Q00372Q01001227000100023Q00200800010001000300200800010001002700061E0001002C2Q013Q00044D3Q002C2Q01001227000100023Q00200800010001000300200800010001002700200800010001002E00061D000100372Q01000100044D3Q00372Q01001227000100023Q00200800010001000300200800010001002F00061E000100392Q013Q00044D3Q00392Q01001227000100023Q00200800010001000300200800010001002F00200800010001003000061E000100392Q013Q00044D3Q00392Q010030243Q0031001F0030243Q0032001F001227000100023Q00200800010001000300200800010001003300061D000100542Q01000100044D3Q00542Q01001227000100023Q00200800010001000300200800010001002700061E000100492Q013Q00044D3Q00492Q01001227000100023Q00200800010001000300200800010001002700200800010001003300061D000100542Q01000100044D3Q00542Q01001227000100023Q00200800010001000300200800010001002F00061E000100572Q013Q00044D3Q00572Q01001227000100023Q00200800010001000300200800010001002F00200800010001001D00061E000100572Q013Q00044D3Q00572Q010030243Q0031001F0030243Q0032001F0030243Q0034002A001227000100023Q00200800010001000300200800010001003500061D000100722Q01000100044D3Q00722Q01001227000100023Q00200800010001000300200800010001002700061E000100672Q013Q00044D3Q00672Q01001227000100023Q00200800010001000300200800010001002700200800010001003500061D000100722Q01000100044D3Q00722Q01001227000100023Q00200800010001000300200800010001002F00061E000100B102013Q00044D3Q00B10201001227000100023Q00200800010001000300200800010001002F00200800010001001900061E000100B102013Q00044D3Q00B1020100203D00013Q00192Q002900010002000100044D3Q00B1020100203D00013Q0009001256000300364Q001000010003000200061D000100842Q01000100044D3Q00842Q0100203D00013Q0009001256000300374Q001000010003000200061D000100842Q01000100044D3Q00842Q0100203D00013Q0009001256000300384Q001000010003000200061E000100972Q013Q00044D3Q00972Q01001227000100023Q00200800010001000300200800010001003900061D000100942Q01000100044D3Q00942Q01001227000100023Q00200800010001000300200800010001002700061E000100B102013Q00044D3Q00B10201001227000100023Q00200800010001000300200800010001002700200800010001003900061E000100B102013Q00044D3Q00B1020100203D00013Q00192Q002900010002000100044D3Q00B1020100203D00013Q00090012560003003A4Q001000010003000200061E000100B72Q013Q00044D3Q00B72Q0100203D00013Q00090012560003003B4Q001000010003000200061D000100B72Q01000100044D3Q00B72Q01001227000100023Q00200800010001000300200800010001003C00061D000100B12Q01000100044D3Q00B12Q01001227000100023Q00200800010001000300200800010001002700061E000100B102013Q00044D3Q00B10201001227000100023Q00200800010001000300200800010001002700200800010001003C00061E000100B102013Q00044D3Q00B102010012270001003E3Q00201600010001003D00202Q00010001003F00104Q003D000100304Q0040001000044Q00B1020100203D00013Q0009001256000300414Q001000010003000200061E0001001D02013Q00044D3Q001D020100203D00013Q0001001227000300424Q001000010003000200061E0001001D02013Q00044D3Q001D0201001227000100023Q00200800010001000300200800010001004300061D000100DC2Q01000100044D3Q00DC2Q01001227000100023Q00200800010001000300200800010001002700061E000100D12Q013Q00044D3Q00D12Q01001227000100023Q00200800010001000300200800010001002700200800010001004300061D000100DC2Q01000100044D3Q00DC2Q01001227000100023Q00200800010001000300200800010001004400061E000100E32Q013Q00044D3Q00E32Q01001227000100023Q00200800010001000300200800010001004400200800010001004500061E000100E32Q013Q00044D3Q00E32Q010012270001003E3Q00204500010001004600202Q00010001004700104Q0046000100304Q0048002A00304Q0049002A00304Q004A004B001227000100023Q00200800010001000300200800010001004C00061D000100FE2Q01000100044D3Q00FE2Q01001227000100023Q00200800010001000300200800010001002700061E000100F32Q013Q00044D3Q00F32Q01001227000100023Q00200800010001000300200800010001002700200800010001004C00061D000100FE2Q01000100044D3Q00FE2Q01001227000100023Q00200800010001000300200800010001004400061E000100FF2Q013Q00044D3Q00FF2Q01001227000100023Q00200800010001000300200800010001004400200800010001001D00061E000100FF2Q013Q00044D3Q00FF2Q010030243Q0034002A001227000100023Q00200800010001000300200800010001004D00061D0001001A0201000100044D3Q001A0201001227000100023Q00200800010001000300200800010001002700061E0001000F02013Q00044D3Q000F0201001227000100023Q00200800010001000300200800010001002700200800010001004D00061D0001001A0201000100044D3Q001A0201001227000100023Q00200800010001000300200800010001004400061E000100B102013Q00044D3Q00B10201001227000100023Q00200800010001000300200800010001004400200800010001001900061E000100B102013Q00044D3Q00B1020100203D00013Q00192Q002900010002000100044D3Q00B1020100203D00013Q00090012560003004E4Q001000010003000200061E0001003402013Q00044D3Q00340201001227000100023Q00200800010001000300200800010001004F00061D000100320201000100044D3Q00320201001227000100023Q00200800010001000300200800010001002700061E000100B102013Q00044D3Q00B10201001227000100023Q00200800010001000300200800010001002700200800010001004F00061E000100B102013Q00044D3Q00B102010030243Q0050001F00044D3Q00B1020100203D00013Q00090012560003003B4Q001000010003000200061E000100B102013Q00044D3Q00B10201001227000100023Q00200800010001000300200800010001005100061D000100540201000100044D3Q00540201001227000100023Q00200800010001000300200800010001002700061E0001004902013Q00044D3Q00490201001227000100023Q00200800010001000300200800010001002700200800010001005100061D000100540201000100044D3Q00540201001227000100023Q00200800010001000300200800010001005200061E0001005A02013Q00044D3Q005A0201001227000100023Q00200800010001000300200800010001005200200800010001004500061E0001005A02013Q00044D3Q005A02010030243Q0053005400302D3Q0040001000122Q0001003E3Q00202Q00010001003D00202Q00010001003F00104Q003D0001001227000100023Q00200800010001000300200800010001005500061D000100750201000100044D3Q00750201001227000100023Q00200800010001000300200800010001002700061E0001006A02013Q00044D3Q006A0201001227000100023Q00200800010001000300200800010001002700200800010001005500061D000100750201000100044D3Q00750201001227000100023Q00200800010001000300200800010001005200061E0001007C02013Q00044D3Q007C0201001227000100023Q00200800010001000300200800010001005200200800010001001D00061E0001007C02013Q00044D3Q007C02010030243Q001E001F00300A3Q0053005400304Q0040001000122Q0001003E3Q00202Q00010001003D00202Q00010001003F00104Q003D0001001227000100023Q00200800010001000300200800010001005200061E0001008802013Q00044D3Q00880201001227000100023Q00200800010001000300200800010001005200200800010001001700061E0001008802013Q00044D3Q008802010030243Q00560016001227000100023Q00200800010001000300200800010001005200061E0001009402013Q00044D3Q00940201001227000100023Q00200800010001000300200800010001005200200800010001001300061E0001009402013Q00044D3Q009402010030243Q00150016001227000100023Q00200800010001000300200800010001005700061D000100AF0201000100044D3Q00AF0201001227000100023Q00200800010001000300200800010001002700061E000100A402013Q00044D3Q00A40201001227000100023Q00200800010001000300200800010001002700200800010001005700061D000100AF0201000100044D3Q00AF0201001227000100023Q00200800010001000300200800010001005200061E000100B102013Q00044D3Q00B10201001227000100023Q00200800010001000300200800010001005200200800010001001900061E000100B102013Q00044D3Q00B1020100203D00013Q00192Q00290001000200012Q002F3Q00017Q001E3Q0003023Q005F4703083Q0053652Q74696E677303123Q004C6F7720576174657220477261706869637303053Q004F7468657203093Q00776F726B737061636503153Q0046696E6446697273744368696C644F66436C612Q7303073Q0054652Q7261696E03043Q007461736B03043Q0077616974030D3Q0057617465725761766553697A65028Q00030E3Q0057617465725761766553702Q656403103Q0057617465725265666C656374616E636503113Q0057617465725472616E73706172656E637903113Q0073657468692Q64656E70726F7065727479030A3Q004465636F726174696F6E03073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C6503073Q005B74617875735D03043Q005465787403503Q00596F7572206578706C6F697420646F6573206E6F742073752Q706F72742073657468692Q64656E70726F70657274792C20706C656173652075736520612064692Q666572656E74206578706C6F69742E03083Q004475726174696F6E026Q00144003073Q0042752Q746F6E3103043Q004F6B617903043Q007761726E03113Q0053656E644E6F74696669636174696F6E73031A3Q004C6F7720576174657220477261706869637320456E61626C6564030B3Q00436F6E736F6C654C6F677300603Q0012273Q00013Q0020085Q00020020085Q000300061D3Q00100001000100044D3Q001000010012273Q00013Q0020085Q00020020085Q000400061E3Q005F00013Q00044D3Q005F00010012273Q00013Q0020085Q00020020085Q00040020085Q000300061E3Q005F00013Q00044D3Q005F00010012273Q00053Q00203D5Q0006001256000200074Q00103Q0002000200061D3Q001F0001000100044D3Q001F00010012273Q00083Q0020155Q00096Q0001000100124Q00053Q00206Q000600122Q000200078Q0002000200064Q001600013Q00044D3Q001600010012273Q00053Q00204C5Q000600122Q000200078Q0002000200304Q000A000B00124Q00053Q00206Q000600122Q000200078Q0002000200304Q000C000B00124Q00053Q00206Q000600122Q000200078Q0002000200304Q000D000B00124Q00053Q00206Q000600122Q000200078Q0002000200304Q000E000B00124Q000F3Q00064Q003F00013Q00044D3Q003F00010012273Q000F3Q001242000100053Q00202Q00010001000600122Q000300076Q00010003000200122Q000200106Q00039Q000003000100044Q004B00012Q00037Q00204F5Q001100122Q000200126Q00033Q000400302Q00030013001400302Q00030015001600302Q00030017001800302Q00030019001A6Q000300010012273Q001B3Q001256000100164Q00293Q000200010012273Q00013Q0020085Q001C00061E3Q005800013Q00044D3Q005800012Q00037Q00204F5Q001100122Q000200126Q00033Q000400302Q00030013001400302Q00030015001D00302Q00030017001800302Q00030019001A6Q000300010012273Q00013Q0020085Q001E00061E3Q005F00013Q00044D3Q005F00010012273Q001B3Q0012560001001D4Q00293Q000200012Q002F3Q00017Q001B3Q0003023Q005F4703083Q0053652Q74696E6773030A3Q004E6F20536861646F777303053Q004F74686572030D3Q00476C6F62616C536861646F7773010003063Q00466F67456E64023Q00C088C30042030E3Q00536861646F77536F66746E652Q73028Q0003113Q0073657468692Q64656E70726F7065727479030A3Q00546563686E6F6C6F6779027Q004003073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C6503073Q005B74617875735D03043Q005465787403503Q00596F7572206578706C6F697420646F6573206E6F742073752Q706F72742073657468692Q64656E70726F70657274792C20706C656173652075736520612064692Q666572656E74206578706C6F69742E03083Q004475726174696F6E026Q00144003073Q0042752Q746F6E3103043Q004F6B617903043Q007761726E03113Q0053656E644E6F74696669636174696F6E7303123Q004E6F20536861646F777320456E61626C6564030B3Q00436F6E736F6C654C6F677300403Q0012273Q00013Q0020085Q00020020085Q000300061D3Q00100001000100044D3Q001000010012273Q00013Q0020085Q00020020085Q000400061E3Q003F00013Q00044D3Q003F00010012273Q00013Q0020085Q00020020085Q00040020085Q000300061E3Q003F00013Q00044D3Q003F00012Q00037Q00304E3Q000500069Q0000304Q000700089Q0000304Q0009000A00124Q000B3Q00064Q001F00013Q00044D3Q001F00010012273Q000B4Q004700015Q00122Q0002000C3Q00122Q0003000D8Q0003000100044Q002B00012Q00033Q00013Q00204F5Q000E00122Q0002000F6Q00033Q000400302Q00030010001100302Q00030012001300302Q00030014001500302Q0003001600176Q000300010012273Q00183Q001256000100134Q00293Q000200010012273Q00013Q0020085Q001900061E3Q003800013Q00044D3Q003800012Q00033Q00013Q00204F5Q000E00122Q0002000F6Q00033Q000400302Q00030010001100302Q00030012001A00302Q00030014001500302Q0003001600176Q000300010012273Q00013Q0020085Q001B00061E3Q003F00013Q00044D3Q003F00010012273Q00183Q0012560001001A4Q00293Q000200012Q002F3Q00017Q00183Q0003023Q005F4703083Q0053652Q74696E6773030D3Q004C6F772052656E646572696E6703053Q004F7468657203083Q0073652Q74696E677303093Q0052656E646572696E67030C3Q005175616C6974794C6576656C026Q00F03F03133Q004D6573685061727444657461696C4C6576656C03043Q00456E756D03073Q004C6576656C303403113Q0053656E644E6F74696669636174696F6E7303073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C6503073Q005B74617875735D03043Q005465787403153Q004C6F772052656E646572696E6720456E61626C656403083Q004475726174696F6E026Q00144003073Q0042752Q746F6E3103043Q004F6B6179030B3Q00436F6E736F6C654C6F677303043Q007761726E00303Q0012273Q00013Q0020085Q00020020085Q000300061D3Q00100001000100044D3Q001000010012273Q00013Q0020085Q00020020085Q000400061E3Q002F00013Q00044D3Q002F00010012273Q00013Q0020085Q00020020085Q00040020085Q000300061E3Q002F00013Q00044D3Q002F00010012273Q00054Q00263Q0001000200206Q000600304Q0007000800124Q00058Q0001000200206Q000600122Q0001000A3Q00202Q00010001000900202Q00010001000B00104Q0009000100124Q00013Q00206Q000C00064Q002800013Q00044D3Q002800012Q00037Q00204F5Q000D00122Q0002000E6Q00033Q000400302Q0003000F001000302Q00030011001200302Q00030013001400302Q0003001500166Q000300010012273Q00013Q0020085Q001700061E3Q002F00013Q00044D3Q002F00010012273Q00183Q001256000100124Q00293Q000200012Q002F3Q00017Q00163Q0003023Q005F4703083Q0053652Q74696E6773030F3Q005265736574204D6174657269616C7303053Q004F7468657203053Q007061697273030B3Q004765744368696C6472656E03073Q0044657374726F7903103Q0055736532302Q324D6174657269616C73010003113Q0053656E644E6F74696669636174696F6E7303073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C6503073Q005B74617875735D03043Q005465787403173Q005265736574204D6174657269616C7320456E61626C656403083Q004475726174696F6E026Q00144003073Q0042752Q746F6E3103043Q004F6B6179030B3Q00436F6E736F6C654C6F677303043Q007761726E00313Q0012273Q00013Q0020085Q00020020085Q000300061D3Q00100001000100044D3Q001000010012273Q00013Q0020085Q00020020085Q000400061E3Q003000013Q00044D3Q003000010012273Q00013Q0020085Q00020020085Q00040020085Q000300061E3Q003000013Q00044D3Q003000010012273Q00054Q002000015Q00202Q0001000100064Q000100029Q00000200044Q0018000100203D0005000400072Q00290005000200010006123Q00160001000200044D3Q001600012Q00037Q0030243Q000800090012273Q00013Q0020085Q000A00061E3Q002900013Q00044D3Q002900012Q00033Q00013Q00204F5Q000B00122Q0002000C6Q00033Q000400302Q0003000D000E00302Q0003000F001000302Q00030011001200302Q0003001300146Q000300010012273Q00013Q0020085Q001500061E3Q003000013Q00044D3Q003000010012273Q00163Q001256000100104Q00293Q000200012Q002F3Q00017Q001D3Q0003023Q005F4703083Q0053652Q74696E677303073Q004650532043617003053Q004F7468657203093Q0073657466707363617003043Q007479706503063Q00737472696E6703063Q006E756D62657203083Q00746F6E756D62657203113Q0053656E644E6F74696669636174696F6E7303073Q00536574436F726503103Q0053656E644E6F74696669636174696F6E03053Q005469746C6503073Q005B74617875735D03043Q0054657874030E3Q004650532043612Q70656420746F2003083Q00746F737472696E6703083Q004475726174696F6E026Q00144003073Q0042752Q746F6E3103043Q004F6B6179030B3Q00436F6E736F6C654C6F677303043Q007761726E2Q01024Q0080842E41030C3Q0046505320556E63612Q706564030E3Q0046505320436170204661696C656403043Q006D61746803043Q006875676500B83Q0012273Q00013Q0020085Q00020020085Q000300061D3Q00100001000100044D3Q001000010012273Q00013Q0020085Q00020020085Q000400061E3Q00B700013Q00044D3Q00B700010012273Q00013Q0020085Q00020020085Q00040020085Q000300061E3Q00B700013Q00044D3Q00B700010012273Q00053Q00061E3Q00A900013Q00044D3Q00A900010012273Q00063Q001227000100013Q00200800010001000200200800010001000300061D000100220001000100044D3Q00220001001227000100013Q00200800010001000200200800010001000400061E0001002200013Q00044D3Q00220001001227000100013Q0020080001000100020020080001000100040020080001000100032Q002C3Q000200020026573Q00370001000700044D3Q003700010012273Q00063Q001227000100013Q00200800010001000200200800010001000300061D000100340001000100044D3Q00340001001227000100013Q00200800010001000200200800010001000400061E0001003400013Q00044D3Q00340001001227000100013Q0020080001000100020020080001000100040020080001000100032Q002C3Q000200020026533Q00810001000800044D3Q008100010012273Q00053Q00123E000100093Q00122Q000200013Q00202Q00020002000200202Q00020002000300062Q000200470001000100044D3Q00470001001227000200013Q00200800020002000200200800020002000400061E0002004700013Q00044D3Q00470001001227000200013Q0020080002000200020020080002000200040020080002000200032Q0044000100029Q0000010012273Q00013Q0020085Q000A00061E3Q006800013Q00044D3Q006800012Q00037Q00202A5Q000B00122Q0002000C6Q00033Q000400302Q0003000D000E00122Q000400103Q00122Q000500113Q00122Q000600013Q00202Q00060006000200202Q00060006000300062Q000600620001000100044D3Q00620001001227000600013Q00200800060006000200200800060006000400061E0006006200013Q00044D3Q00620001001227000600013Q0020080006000600020020080006000600040020080006000600032Q002C0005000200022Q002300040004000500102Q0003000F000400302Q00030012001300302Q0003001400156Q000300010012273Q00013Q0020085Q001600061E3Q00B700013Q00044D3Q00B700010012273Q00173Q001204000100103Q00122Q000200113Q00122Q000300013Q00202Q00030003000200202Q00030003000300062Q0003007D0001000100044D3Q007D0001001227000300013Q00200800030003000200200800030003000400061E0003007D00013Q00044D3Q007D0001001227000300013Q0020080003000300020020080003000300040020080003000300032Q002C0002000200022Q00090001000100022Q00293Q0002000100044D3Q00B700010012273Q00013Q0020085Q00020020085Q000300061D3Q00910001000100044D3Q009100010012273Q00013Q0020085Q00020020085Q000400061E3Q008F00013Q00044D3Q008F00010012273Q00013Q0020085Q00020020085Q00040020085Q00030026533Q00B70001001800044D3Q00B700010012273Q00053Q00120B000100198Q0002000100124Q00013Q00206Q000A00064Q00A100013Q00044D3Q00A100012Q00037Q00204F5Q000B00122Q0002000C6Q00033Q000400302Q0003000D000E00302Q0003000F001A00302Q00030012001300302Q0003001400156Q000300010012273Q00013Q0020085Q001600061E3Q00B700013Q00044D3Q00B700010012273Q00173Q0012560001001A4Q00293Q0002000100044D3Q00B700012Q00037Q0020185Q000B00122Q0002000C6Q00033Q000400302Q0003000D000E00302Q0003000F001B00122Q0004001C3Q00202Q00040004001D00102Q00030012000400302Q0003001400156Q0003000100124Q00173Q00122Q0001001B8Q000200012Q002F3Q00017Q00043Q0003043Q007761697403023Q005F47030A3Q004C6F6164656457616974026Q00F03F010B3Q001227000100013Q001227000200023Q00200800020002000300061D000200060001000100044D3Q00060001001256000200044Q00290001000200012Q000300016Q002200026Q00290001000200012Q002F3Q00017Q00", GetFEnv(), ...);
