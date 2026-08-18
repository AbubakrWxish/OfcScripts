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
				if (Enum <= 24) then
					if (Enum <= 11) then
						if (Enum <= 5) then
							if (Enum <= 2) then
								if (Enum <= 0) then
									Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
								elseif (Enum == 1) then
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									do
										return;
									end
								end
							elseif (Enum <= 3) then
								Stk[Inst[2]] = Inst[3];
							elseif (Enum > 4) then
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
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 8) then
							if (Enum <= 6) then
								local A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							elseif (Enum > 7) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							elseif Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 9) then
							Stk[Inst[2]] = {};
						elseif (Enum == 10) then
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
						else
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 17) then
						if (Enum <= 14) then
							if (Enum <= 12) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum > 13) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
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
									if (Mvm[1] == 21) then
										Indexes[Idx - 1] = {Stk,Mvm[3]};
									else
										Indexes[Idx - 1] = {Upvalues,Mvm[3]};
									end
									Lupvals[#Lupvals + 1] = Indexes;
								end
								Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
							end
						elseif (Enum <= 15) then
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum == 16) then
							Stk[Inst[2]] = {};
						else
							local A = Inst[2];
							local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
							local Edx = 0;
							for Idx = A, Inst[4] do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 20) then
						if (Enum <= 18) then
							local A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						elseif (Enum > 19) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 22) then
						if (Enum == 21) then
							Stk[Inst[2]] = Stk[Inst[3]];
						elseif not Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 23) then
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
						VIP = VIP + 1;
					else
						VIP = Inst[3];
					end
				elseif (Enum <= 37) then
					if (Enum <= 30) then
						if (Enum <= 27) then
							if (Enum <= 25) then
								local A = Inst[2];
								local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								local Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
							elseif (Enum == 26) then
								Stk[Inst[2]] = Inst[3];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							end
						elseif (Enum <= 28) then
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
								if (Mvm[1] == 21) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						elseif (Enum == 29) then
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						else
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						end
					elseif (Enum <= 33) then
						if (Enum <= 31) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						elseif (Enum > 32) then
							Stk[Inst[2]] = Upvalues[Inst[3]];
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 35) then
						if (Enum == 34) then
							do
								return;
							end
						elseif Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum > 36) then
						Stk[Inst[2]] = Upvalues[Inst[3]];
					else
						local A = Inst[2];
						Stk[A] = Stk[A]();
					end
				elseif (Enum <= 43) then
					if (Enum <= 40) then
						if (Enum <= 38) then
							Stk[Inst[2]] = Env[Inst[3]];
						elseif (Enum > 39) then
							local A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A = Inst[2];
							local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							local Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 41) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					elseif (Enum > 42) then
						if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum <= 46) then
					if (Enum <= 44) then
						Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
					elseif (Enum == 45) then
						local A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					else
						local A = Inst[2];
						local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
						Top = (Limit + A) - 1;
						local Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
					end
				elseif (Enum <= 48) then
					if (Enum == 47) then
						VIP = Inst[3];
					else
						Stk[Inst[2]][Inst[3]] = Inst[4];
					end
				elseif (Enum == 49) then
					local A = Inst[2];
					Stk[A] = Stk[A](Stk[A + 1]);
				else
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!2C3Q00030A3Q006C6F6164737472696E6703043Q0067616D6503073Q00482Q747047657403493Q00682Q7470733A2Q2F6769746875622E636F6D2F64617769642D736372697074732F466C75656E742F72656C65617365732F6C61746573742F646F776E6C6F61642F6D61696E2E6C7561030C3Q0043726561746557696E646F7703053Q005469746C65030F3Q00416E696D616C20486F73706974616C03083Q005375625469746C65030F3Q0062792041627562616B72577869736803083Q005461625769647468026Q00644003043Q0053697A6503053Q005544696D32030A3Q0066726F6D4F2Q66736574025Q00E07F40025Q00A0744003073Q00416372796C6963010003053Q005468656D6503043Q004461726B030B3Q004D696E696D697A654B657903043Q00456E756D03073Q004B6579436F646503013Q004D03043Q004D61696E03063Q00412Q64546162030E3Q00D093D0BBD0B0D0B2D0BDD18BD0B903043Q0049636F6E03053Q00686F75736503083Q0053652Q74696E677303123Q00D09DD0B0D181D182D180D0BED0B9D0BAD0B803083Q0073652Q74696E6773030A3Q004765745365727669636503073Q00506C6179657273030B3Q004C6F63616C506C6179657203093Q00412Q64546F2Q676C6503093Q00496E7374616E742Q50031D3Q00D091D18BD181D182D180D18BD0B520D0BFD180D0BED0BCD0BFD182D18B03073Q0044656661756C7403093Q004F6E4368616E67656403093Q00457370546F2Q676C65031F3Q00D09FD0BED0BAD0B0D0B7D0B0D182D18C20D0B8D0B3D180D0BED0BAD0BED0B203093Q0053656C656374546162026Q00F03F00493Q00120B3Q00013Q00120B000100023Q00201E00010001000300121A000300044Q0027000100034Q000C5Q00022Q00243Q0001000200201E00013Q00052Q000900033Q000700302A00030006000700302A00030008000900302A0003000A000B00120B0004000D3Q00201700040004000E00121A0005000F3Q00121A000600104Q002D0004000600020010080003000C000400302A00030011001200302A00030013001400120B000400163Q0020170004000400170020170004000400180010080003001500042Q002D0001000300022Q000900023Q000200201E00030001001A2Q000900053Q000200302A00050006001B00302A0005001C001D2Q002D00030005000200100800020019000300201E00030001001A2Q000900053Q000200302A00050006001F00302A0005001C00202Q002D0003000500020010080002001E000300120B000300023Q00201E00030003002100121A000500224Q002D00030005000200201700040003002300022C00055Q00022C000600013Q00201700070002001900201E00070007002400121A000900254Q0009000A3Q000200302A000A0006002600302A000A002700122Q002D0007000A000200201E00080007002800022C000A00024Q00120008000A000100201700080002001900201E00080008002400121A000A00294Q0009000B3Q000200302A000B0006002A00302A000B002700122Q002D0008000B000200201E00090008002800060D000B0003000100042Q00153Q00034Q00153Q00044Q00153Q00054Q00153Q00064Q00120009000B000100201E00090001002B00121A000B002C4Q00120009000B00012Q00023Q00013Q00043Q00143Q00030E3Q0046696E6446697273744368696C6403133Q00506C617965724553505F486967686C6967687403083Q00496E7374616E63652Q033Q006E657703093Q00486967686C6967687403043Q004E616D6503073Q0041646F726E2Q6503063Q00506172656E7403093Q0046692Q6C436F6C6F7203063Q00436F6C6F723303073Q0066726F6D524742026Q005440026Q006940026Q005E40030C3Q004F75746C696E65436F6C6F72025Q00E06F4003103Q0046692Q6C5472616E73706172656E6379026Q00E03F03133Q004F75746C696E655472616E73706172656E6379028Q00011D3Q00201E00013Q000100121A000300024Q002D0001000300020006160001001C000100010004203Q001C000100120B000100033Q00201700010001000400121A000200054Q000400010002000200302A000100060002001008000100073Q001008000100083Q00120B0002000A3Q00201700020002000B00121A0003000C3Q00121A0004000D3Q00121A0005000E4Q002D00020005000200100800010009000200120B0002000A3Q00201700020002000B00121A000300103Q00121A000400103Q00121A000500104Q002D0002000500020010080001000F000200302A00010011001200302A0001001300142Q00023Q00017Q00033Q00030E3Q0046696E6446697273744368696C6403133Q00506C617965724553505F486967686C6967687403073Q0044657374726F7901083Q00201E00013Q000100121A000300024Q002D0001000300020006070001000700013Q0004203Q0007000100201E0002000100032Q00010002000200012Q00023Q00017Q00043Q0003023Q005F47030A3Q00496E7374616E742Q507303043Q007461736B03053Q00737061776E01073Q00120B000100013Q001008000100023Q00120B000100033Q00201700010001000400022C00026Q00010001000200012Q00023Q00013Q00013Q000C3Q0003023Q005F47030A3Q00496E7374616E742Q507303043Q007461736B03043Q0077616974029A5Q99E93F03053Q00706169727303093Q00776F726B7370616365030E3Q0047657444657363656E64616E74732Q033Q00497341030F3Q0050726F78696D69747950726F6D7074030C3Q00486F6C644475726174696F6E029Q00183Q00120B3Q00013Q0020175Q00020006073Q001700013Q0004203Q0017000100120B3Q00033Q0020175Q000400121A000100054Q00013Q0002000100120B3Q00063Q00120B000100073Q00201E0001000100082Q001D000100024Q00195Q00020004203Q0014000100201E00050004000900121A0007000A4Q002D0005000700020006070005001400013Q0004203Q0014000100302A0004000B000C0006053Q000E000100020004203Q000E00010004205Q00012Q00023Q00017Q00053Q0003023Q005F4703063Q00457370506C7203063Q00697061697273030A3Q00476574506C617965727303093Q00436861726163746572011C3Q00120B000100013Q001008000100023Q00120B000100034Q002500025Q00201E0002000200042Q001D000200034Q001900013Q00030004203Q001900012Q0025000600013Q00062B00050019000100060004203Q001900010020170006000500050006070006001900013Q0004203Q0019000100120B000600013Q0020170006000600020006070006001600013Q0004203Q001600012Q0025000600023Q0020170007000500052Q00010006000200010004203Q001900012Q0025000600033Q0020170007000500052Q000100060002000100060500010008000100020004203Q000800012Q00023Q00017Q00", GetFEnv(), ...);